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

    type SNode<'k,'v> = {key: 'k; value: 'v}

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
                        | SNode sn -> if equals sn.key k then Result (Some sn.value) else Result None

            | TNode _ -> clean parent level; Restart
            | LNode ln -> Result (List.tryFind (fst >> equals k) ln |> Option.bind (snd >> Some))

    let rec lookup' equals hashCode trie k =
        let r = Volatile.Read (ref trie.root)
        let result = ilookup equals hashCode r k 0 None
        match result with
            | Restart -> lookup' equals hashCode trie k
            | Result r -> r
            
    let lookup trie k = lookup' (=) hash trie k

type CTrie() = 
    member this.X = "F#"
