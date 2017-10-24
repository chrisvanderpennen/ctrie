namespace CTrie
open System.Threading

module FSharp =
    let BitmapLength=5
    
    let bitcount (i: uint32) =
        let mutable i = i
        i <- ((i >>> 1) &&& 0x55555555u)
        i <- (i &&& 0x33333333u) + ((i >>> 2) &&& 0x33333333u)
        (((i + (i >>> 4)) &&& 0x0f0f0f0fu) * 0x01010101u) >>> 24
    
    let flagpos hc bmp lev =
        let index = (hc >>> lev) &&& 0x1f
        let flag = 1u <<< index
        let pos = bitcount (bmp &&& (flag - 1u))
        (flag, pos)
    
    let flagUnset i bmp =
        i &&& bmp = 0u

    type SNode<'k,'v> = ('k * 'v)

    type TNode<'k,'v> = {sn: SNode<'k,'v>}

    type CNode<'k,'v> = {bitmap: uint32; array: Branch<'k,'v>[]}
    
    and INode<'k,'v> = {main: MainNode<'k,'v>; gen: obj}
    
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
        gen: obj
    }

    type Result<'v> =
        Restart
        | Result of 'v option

    let resurrectINode i =
        match i.main with
            | TNode tn -> SNode tn.sn
            | _ -> INode i

    let resurrect n =
        match n with
            | INode i -> match i.main with
                            | TNode tn -> SNode tn.sn
                            | _ -> INode i
            | SNode _ -> n

    let toContracted cn lev =
        if lev > 0 && cn.array.Length = 1 then
            match cn.array.[0] with
                | SNode sn -> TNode { sn = sn }
                | _ -> CNode cn
        else CNode cn

    let toCompressed cn lev =
        let ncn = {bitmap=cn.bitmap; array=Array.map resurrect cn.array}
        toContracted ncn lev

    let clean i lev =
        match i with
            | Some node -> 
                let m = Volatile.Read (ref node.main)
                match m with
                    | CNode cn -> ignore(Interlocked.CompareExchange(ref node.main, m, toCompressed cn lev))
                    | _ -> ()
            | None -> ()

    let rec ilookup equals hashCode i k level parent =
        match Volatile.Read (ref i.main) with
            | CNode cn -> 
                let flag, pos = flagpos (hashCode k) cn.bitmap level
                if (cn.bitmap &&& flag) = 0u
                    then Result None
                else
                    match cn.array.[int32 pos] with
                        | INode sin -> ilookup equals hashCode sin k (level + BitmapLength) (Some i)
                        | SNode sn -> if equals (fst sn) k then Result (Some (snd sn)) else Result None

            | TNode _ -> clean parent level; Restart
            | LNode ln -> Result (List.tryFind (fst >> equals k) ln |> Option.bind (snd >> Some))

    let rec lookup' equals hashCode trie k =
        let r = Volatile.Read (ref trie.root)
        let result = ilookup equals hashCode r k 0 None
        match result with
            | Restart -> lookup' equals hashCode trie k
            | Result r -> r
            
    let lookup trie k = lookup' (=) hash trie k

    let CAS<'t when 't: not struct> (loc: 't ref) x y =
        LanguagePrimitives.PhysicalEquality x (Interlocked.CompareExchange(loc,x,y))

    let rec createCNode hashcode a b lev gen =
        let array = Array.zeroCreate 32
        let aflag, apos = flagpos (hashcode (fst a)) 0u lev
        let bitmap, bpos = flagpos (hashcode (fst b)) aflag lev
        if apos = bpos then
            if lev > 32 then
                let inode = INode { main=LNode [a;b]; gen=gen }
                Array.set array (int32 apos) inode
            else
                let inode = INode { main=createCNode hashcode a b (lev+BitmapLength) gen; gen=gen }
                Array.set array (int32 apos) inode
        else
            Array.set array (int32 apos) (SNode a)
            Array.set array (int32 bpos) (SNode b)
        CNode { array=array; bitmap=bitmap }

    let updateCNode cn pos node =
        let array = Array.copy cn.array
        Array.set array (int32 pos) node
        CNode { bitmap=cn.bitmap; array=array; }

    let rec iinsert equals hashCode i k v lev parent gen =
        let n = Volatile.Read (ref i.main)
        match n with
            | CNode cn ->
                let flag, pos = flagpos (hashCode k) cn.bitmap lev
                if flagUnset flag cn.bitmap then
                    let narr = Array.copy cn.array
                    Array.set narr (int32 pos) (SNode (k, v))
                    CAS (ref i.main) n (CNode {array=narr; bitmap=cn.bitmap|||flag})
                else
                    match cn.array.[int32 pos] with
                        | INode _ -> iinsert equals hashCode i k v (lev + BitmapLength) (Some i) gen
                        | SNode sn ->
                            if not(equals k (fst sn)) then
                                let nin = INode { main=createCNode hashCode sn (k, v) (lev + BitmapLength) gen; gen=gen }
                                let ncn = updateCNode cn pos nin
                                CAS (ref i.main) n ncn
                            else
                                let ncn = updateCNode cn pos (SNode (k, v))
                                CAS (ref i.main) n ncn
            | TNode _ -> clean parent (lev - BitmapLength); false
            | LNode ln -> CAS (ref i.main) n (LNode ((k, v) :: ln))

    let rec insert' equals hashCode trie k v =
        let r = Volatile.Read (ref trie.root)
        match iinsert equals hashCode r k v 0 None trie.gen with
            | true -> true
            | false -> insert' equals hashCode trie k v

    let insert trie k v = insert' (=) hash trie k v

type CTrie() = 
    class end
