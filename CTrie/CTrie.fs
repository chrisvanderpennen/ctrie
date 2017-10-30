namespace CTrie
open System.Threading

module FSharp =
    [<Literal>] 
    let private BitmapLength=5
    
    type internal SNode<'k,'v> = ('k * 'v)

    type internal TNode<'k,'v> = {sn: SNode<'k,'v>}

    type internal CNode<'k,'v> = {bitmap: int; array: Branch<'k,'v>[]}
    
    and internal INode<'k,'v>(main, generation) =
        let mutable main: MainNode<'k,'v> = main
        let generation: obj = generation

        member this.Read () =
            Volatile.Read &main

        member self.TryUpdate currentMain newMain =
            LanguagePrimitives.PhysicalEquality 
                currentMain 
                (Interlocked.CompareExchange(&main,currentMain,newMain))
    
    and internal MainNode<'k,'v> =
        CN of CNode<'k,'v>
        | TN of TNode<'k,'v>
        | LN of ('k * 'v) list
    
    and internal Branch<'k,'v> =
        IN of INode<'k,'v>
        | SN of SNode<'k,'v>

    type Result<'v> =
        Restart
        | Result of 'v option

    let inline private bitcount (i) =
        let mutable i = i
        i <- ((i >>> 1) &&& 0x55555555)
        i <- (i &&& 0x33333333) + ((i >>> 2) &&& 0x33333333)
        (((i + (i >>> 4)) &&& 0x0f0f0f0f) * 0x01010101) >>> 24
    
    let inline private flagpos hc bmp lev =
        let index = (hc >>> lev) &&& 0x1f
        let flag = 1 <<< index
        let pos = bitcount (bmp &&& (flag - 1))
        flag, pos
    
    let inline private flagUnset i bmp =
        i &&& bmp = 0

    let private resurrect n =
        match n with
            | IN i -> match i.Read () with
                            | TN tn -> SN tn.sn
                            | _ -> IN i
            | SN _ -> n

    let rec private createCNode hashcode a b lev gen =
        let array = Array.zeroCreate 32
        let aflag, apos = flagpos (hashcode (fst a)) 0 lev
        let bitmap, bpos = flagpos (hashcode (fst b)) aflag lev
        if apos = bpos then
            if lev > 32 then
                let inode = IN (INode (LN [a;b], gen))
                Array.set array (int32 apos) inode
            else
                let inode = IN (INode (createCNode hashcode a b (lev+BitmapLength) gen, gen))
                Array.set array (int32 apos) inode
        else
            Array.set array (int32 apos) (SN a)
            Array.set array (int32 bpos) (SN b)
        CN { array=array; bitmap=bitmap }

    let private updateCNode cn pos node =
        let array = Array.copy cn.array
        Array.set array (int32 pos) node
        CN { bitmap=cn.bitmap; array=array; }

    let private toContracted cn lev =
        if lev > 0 && cn.array.Length = 1 then
            match cn.array.[0] with
                | SN sn -> TN { sn = sn }
                | _ -> CN cn
        else CN cn

    let private toCompressed cn lev =
        let ncn = {bitmap=cn.bitmap; array=Array.map resurrect cn.array}
        toContracted ncn lev

    let private clean (inode: INode<'a,'b> option) lev =
        match inode with
            | Some node -> 
                let m = node.Read ()
                match m with
                    | CN cn -> ignore(node.TryUpdate m (toCompressed cn lev))
                    | _ -> ()
            | None -> ()

    let rec private ilookup equals hashCode (inode: INode<'a,'b>) key level parent =
        match inode.Read () with
            | CN cn -> 
                let flag, pos = flagpos (hashCode key) cn.bitmap level
                if (cn.bitmap &&& flag) = 0
                    then Result None
                else
                    match cn.array.[int32 pos] with
                        | IN sin -> ilookup equals hashCode sin key (level + BitmapLength) (Some inode)
                        | SN sn -> if equals (fst sn) key then Result (Some (snd sn)) else Result None

            | TN _ -> clean parent level; Restart
            | LN ln -> Result (List.tryFind (fst >> equals key) ln |> Option.bind (snd >> Some))

    let rec private iinsert equals hashCode (inode: INode<'a,'b>) key value level parent generation =
        let n = inode.Read ()
        match n with
            | CN cn ->
                let flag, pos = flagpos (hashCode key) cn.bitmap level
                if flagUnset flag cn.bitmap then
                    let narr = Array.copy cn.array
                    Array.set narr (int32 pos) (SN (key, value))
                    inode.TryUpdate n (CN {array=narr; bitmap=cn.bitmap|||flag})
                else
                    match cn.array.[int32 pos] with
                        | IN _ -> iinsert equals hashCode inode key value (level + BitmapLength) (Some inode) generation
                        | SN sn ->
                            if not(equals key (fst sn)) then
                                let nin = IN (INode (createCNode hashCode sn (key, value) (level + BitmapLength) generation, generation))
                                let ncn = updateCNode cn pos nin
                                inode.TryUpdate n ncn
                            else
                                let ncn = updateCNode cn pos (SN (key, value))
                                inode.TryUpdate n ncn
            | TN _ -> clean parent (level - BitmapLength); false
            | LN ln -> inode.TryUpdate n (LN ((key, value) :: ln))

    type CTrie<'k,'v>(equals, hashCode, readonly) =
        let equals = equals
        let hashCode = hashCode
        let mutable generation = new obj ()
        let mutable root: INode<'k,'v> = INode( CN { bitmap=0; array=Array.zeroCreate 32 }, generation )

        member val internal ReadOnly = readonly
        member internal self.Generation
            with get() =
                generation
        member internal self.Read () =
            Volatile.Read &root

    let rec lookup' equals hashCode (trie: CTrie<'a,'b>) key =
        let r = trie.Read ()
        let result = ilookup equals hashCode r key 0 None
        match result with
            | Restart -> lookup' equals hashCode trie key
            | Result r -> r
            
    let rec insert' equals hashCode (trie: CTrie<'a,'b>) key value =
        if trie.ReadOnly then false else
        let r = trie.Read ()
        match iinsert equals hashCode r key value 0 None trie.Generation with
            | true -> true
            | false -> insert' equals hashCode trie key value

    let lookup trie key = lookup' (=) hash trie key
    let insert trie key value = insert' (=) hash trie key value


type CTrie() = 
    class end
