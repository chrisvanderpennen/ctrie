namespace CTrie
open System.Threading

type internal SNode<'k,'v> = ('k * 'v)

type internal TNode<'k,'v> = {sn: SNode<'k,'v>}

type internal CNode<'k,'v> = {bitmap: int; array: Branch<'k,'v>[]}

and internal INode<'k,'v>(main, generation) =
    [<VolatileField>]
    let mutable main: MainNode<'k,'v> = main
    let generation: obj = generation

    member this.ReadMain () =
        Volatile.Read &main

    member self.TryUpdate currentMain newMain =
        LanguagePrimitives.PhysicalEquality 
            currentMain 
            (Interlocked.CompareExchange(&main,newMain,currentMain))

and internal MainNode<'k,'v> =
    CN of CNode<'k,'v>
    | TN of TNode<'k,'v>
    | LN of SNode<'k,'v> list

and internal Branch<'k,'v> =
    IN of INode<'k,'v>
    | SN of SNode<'k,'v>

module CTrie =
    [<Literal>] 
    let private BitmapLength=5
    
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
            | IN i -> match i.ReadMain () with
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
                Array.set array apos inode
            else
                let inode = IN (INode (createCNode hashcode a b (lev+BitmapLength) gen, gen))
                Array.set array apos inode
        else
            Array.set array apos (SN a)
            Array.set array bpos (SN b)
        CN { array=array; bitmap=bitmap }

    let private updateCNode cn pos node =
        let array = Array.copy cn.array
        Array.set array pos node
        CN { bitmap=cn.bitmap; array=array; }

    let private removeCNode cn flag pos =
        let array = Array.copy cn.array
        Array.set array pos Unchecked.defaultof<Branch<'a,'b>>
        { bitmap=cn.bitmap &&& ~~~flag; array=array }

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
                let m = node.ReadMain ()
                match m with
                    | CN cn -> ignore(node.TryUpdate m (toCompressed cn lev))
                    | _ -> ()
            | None -> ()

    let rec internal ilookup equals hashCode (inode: INode<'a,'b>) key level parent =
        match inode.ReadMain () with
            | CN cn -> 
                let flag, pos = flagpos (hashCode key) cn.bitmap level
                if (cn.bitmap &&& flag) = 0
                    then Result None
                else
                    match cn.array.[pos] with
                        | IN sin -> ilookup equals hashCode sin key (level + BitmapLength) (Some inode)
                        | SN sn -> if equals (fst sn) key then Result (Some (snd sn)) else Result None

            | TN _ -> clean parent level; Restart
            | LN ln -> Result (List.tryFind (fst >> equals key) ln |> Option.bind (snd >> Some))

    let rec internal iinsert equals hashCode (inode: INode<'a,'b>) key value level parent generation =
        let n = inode.ReadMain ()
        match n with
            | CN cn ->
                let flag, pos = flagpos (hashCode key) cn.bitmap level
                if flagUnset flag cn.bitmap then
                    let narr = Array.copy cn.array
                    Array.set narr pos (SN (key, value))
                    inode.TryUpdate n (CN {array=narr; bitmap=cn.bitmap|||flag})
                else
                    match cn.array.[pos] with
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

    let rec internal iremove equals hashCode (i: INode<'a,'b>) k lev parent =
        let eq = equals k
        let n = i.ReadMain ()
        match n with
            | CN cn ->
                let flag, pos = flagpos (hashCode k) lev cn.bitmap
                if (cn.bitmap &&& flag) = 0 then Result None
                else 
                    match cn.array.[pos] with
                        | IN sin -> iremove equals hashCode sin k (lev+BitmapLength) (Some i)
                        | SN sn ->
                            if (fst >> eq) sn then
                                let ncn = removeCNode cn flag pos 
                                let cntr = toContracted ncn lev
                                if i.TryUpdate n cntr then Result (Some (snd sn))
                                else Restart
                            else Result None
            | TN tn -> clean parent (lev - BitmapLength); Restart
            | LN ln ->
                let nln = List.filter (fst >> eq) ln
                let result = ln |> (List.tryFind (fst >> eq) >> function | Some x -> Some (snd x) | None -> None)
                if nln.Length = 1 then
                    if i.TryUpdate n (TN {sn=nln.Head}) then Result result else Restart
                else if i.TryUpdate n (LN nln) then Result result else Restart

open CTrie
type CTrie<'k,'v>(equals, hashCode, readonly) =
    let equals = equals
    let hashCode = hashCode
    let mutable generation = new obj ()
    
    [<VolatileField>]
    let mutable root: INode<'k,'v> = INode( CN { bitmap=0; array=Array.zeroCreate 32 }, generation )

    let readRoot () =
        Volatile.Read (&root)

    let rec lookup' key =
        let r = readRoot ()
        let result = ilookup equals hashCode r key 0 None
        match result with
            | Restart -> lookup' key
            | Result r -> r
            
    let rec insert' key value =
        if readonly then false else
        let r = readRoot ()
        match iinsert equals hashCode r key value 0 None generation with
            | true -> true
            | false -> insert' key value

    let rec remove' k =
        if readonly then None else
        let r = readRoot ()
        match iremove equals hashCode r k 0 None with
            | Restart -> remove' k
            | Result v -> v

    member val internal ReadOnly = readonly
    member internal self.Generation
        with get() =
            generation
    member internal self.Root
        with get() =
            readRoot ()

    member this.Remove key = remove' key
    member this.Lookup key = lookup' key
    member this.Insert key value = insert' key value

    new(equals, hashCode) = CTrie(equals, hashCode, false)
