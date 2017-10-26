namespace CTrie
open System.Threading

module FSharp =
    [<Literal>] 
    let private BitmapLength=5
    
    type SNode<'k,'v> = ('k * 'v)

    type TNode<'k,'v> = {sn: SNode<'k,'v>}

    type CNode<'k,'v> = {bitmap: uint32; array: Branch<'k,'v>[]}
    
    and INode<'k,'v> = {main: MainNode<'k,'v>; generation: obj}
    
    and MainNode<'k,'v> =
        CNode of CNode<'k,'v>
        | TNode of TNode<'k,'v>
        | LNode of ('k * 'v) list
    
    and Branch<'k,'v> =
        INode of INode<'k,'v>
        | SNode of SNode<'k,'v>

    type CTrie<'k,'v> = {
        root: INode<'k,'v>
        readonly: bool
        generation: obj
    }

    type Result<'v> =
        Restart
        | Result of 'v option

    let inline private bitcount (i: uint32) =
        let mutable i = i
        i <- ((i >>> 1) &&& 0x55555555u)
        i <- (i &&& 0x33333333u) + ((i >>> 2) &&& 0x33333333u)
        (((i + (i >>> 4)) &&& 0x0f0f0f0fu) * 0x01010101u) >>> 24
    
    let inline private flagpos hc bmp lev =
        let index = (hc >>> lev) &&& 0x1f
        let flag = 1u <<< index
        let pos = bitcount (bmp &&& (flag - 1u))
        flag, pos
    
    let inline private flagUnset i bmp =
        i &&& bmp = 0u

    let inline private CAS<'t when 't: not struct> (cell: 't ref) current updated =
        LanguagePrimitives.PhysicalEquality current (Interlocked.CompareExchange(cell,current,updated))

    let private resurrect n =
        match n with
            | INode i -> match i.main with
                            | TNode tn -> SNode tn.sn
                            | _ -> INode i
            | SNode _ -> n

    let rec private createCNode hashcode a b lev gen =
        let array = Array.zeroCreate 32
        let aflag, apos = flagpos (hashcode (fst a)) 0u lev
        let bitmap, bpos = flagpos (hashcode (fst b)) aflag lev
        if apos = bpos then
            if lev > 32 then
                let inode = INode { main=LNode [a;b]; generation=gen }
                Array.set array (int32 apos) inode
            else
                let inode = INode { main=createCNode hashcode a b (lev+BitmapLength) gen; generation=gen }
                Array.set array (int32 apos) inode
        else
            Array.set array (int32 apos) (SNode a)
            Array.set array (int32 bpos) (SNode b)
        CNode { array=array; bitmap=bitmap }

    let private updateCNode cn pos node =
        let array = Array.copy cn.array
        Array.set array (int32 pos) node
        CNode { bitmap=cn.bitmap; array=array; }

    let private toContracted cn lev =
        if lev > 0 && cn.array.Length = 1 then
            match cn.array.[0] with
                | SNode sn -> TNode { sn = sn }
                | _ -> CNode cn
        else CNode cn

    let private toCompressed cn lev =
        let ncn = {bitmap=cn.bitmap; array=Array.map resurrect cn.array}
        toContracted ncn lev

    let private clean i lev =
        match i with
            | Some node -> 
                let m = Volatile.Read (ref node.main)
                match m with
                    | CNode cn -> ignore(Interlocked.CompareExchange(ref node.main, m, toCompressed cn lev))
                    | _ -> ()
            | None -> ()

    let rec private ilookup equals hashCode inode key level parent =
        match Volatile.Read (ref inode.main) with
            | CNode cn -> 
                let flag, pos = flagpos (hashCode key) cn.bitmap level
                if (cn.bitmap &&& flag) = 0u
                    then Result None
                else
                    match cn.array.[int32 pos] with
                        | INode sin -> ilookup equals hashCode sin key (level + BitmapLength) (Some inode)
                        | SNode sn -> if equals (fst sn) key then Result (Some (snd sn)) else Result None

            | TNode _ -> clean parent level; Restart
            | LNode ln -> Result (List.tryFind (fst >> equals key) ln |> Option.bind (snd >> Some))

    let rec lookup' equals hashCode trie key =
        let r = Volatile.Read (ref trie.root)
        let result = ilookup equals hashCode r key 0 None
        match result with
            | Restart -> lookup' equals hashCode trie key
            | Result r -> r
            
    let lookup trie key = lookup' (=) hash trie key

    let rec private iinsert equals hashCode inode key value level parent generation =
        let n = Volatile.Read (ref inode.main)
        match n with
            | CNode cn ->
                let flag, pos = flagpos (hashCode key) cn.bitmap level
                if flagUnset flag cn.bitmap then
                    let narr = Array.copy cn.array
                    Array.set narr (int32 pos) (SNode (key, value))
                    CAS (ref inode.main) n (CNode {array=narr; bitmap=cn.bitmap|||flag})
                else
                    match cn.array.[int32 pos] with
                        | INode _ -> iinsert equals hashCode inode key value (level + BitmapLength) (Some inode) generation
                        | SNode sn ->
                            if not(equals key (fst sn)) then
                                let nin = INode { main=createCNode hashCode sn (key, value) (level + BitmapLength) generation; generation=generation }
                                let ncn = updateCNode cn pos nin
                                CAS (ref inode.main) n ncn
                            else
                                let ncn = updateCNode cn pos (SNode (key, value))
                                CAS (ref inode.main) n ncn
            | TNode _ -> clean parent (level - BitmapLength); false
            | LNode ln -> CAS (ref inode.main) n (LNode ((key, value) :: ln))

    let rec insert' equals hashCode trie key value =
        let r = Volatile.Read (ref trie.root)
        match iinsert equals hashCode r key value 0 None trie.generation with
            | true -> true
            | false -> insert' equals hashCode trie key value

    let insert trie k v = insert' (=) hash trie k v

type CTrie() = 
    class end
