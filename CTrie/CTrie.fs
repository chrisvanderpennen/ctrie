namespace CTrie
open System.Threading

module FSharp =

    let BitmapLength=5
    
    let bitcount (i: uint32) =
        let mutable i = i
        i <- ((i >>> 1) &&& 0x55555555u)
        i <- (i &&& 0x33333333u) + ((i >>> 2) &&& 0x33333333u)
        (((i + (i >>> 4)) &&& 0x0f0f0f0fu) * 0x01010101u) >>> 24
    
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

    let flagpos hc bmp lev =
        let index = (hc >>> lev*BitmapLength) &&& 0x1f
        let flag = 1u <<< index
        let pos = bitcount (bmp &&& (flag - 1u))
        (flag, pos)

    let rec ilookup i k level parent equals hashCode =
        match Volatile.Read (ref i.main) with
            | CNode cn -> 
                let flag, pos = flagpos (hashCode k) cn.bitmap level
                if (cn.bitmap &&& flag) = 0u
                    then Result None
                else
                    match cn.array.[int32 pos] with
                        | INode sin -> ilookup sin k (level + BitmapLength) (Some i) equals hashCode
                        | SNode sn -> if equals sn.key k then Result (Some sn.value) else Result None

            | TNode tn -> Restart
            | LNode ln -> Result (List.tryFind (fst >> (equals k)) ln |> (Option.bind (snd >> Some)))

    let rec lookup (trie: CTrie<'k,'v>) k equals hashCode =
        let r = Volatile.Read (ref trie.root)
        let result = ilookup r k 0 None equals hashCode
        match result with
            | Restart -> lookup trie k equals hashCode
            | Result r -> r

type CTrie() = 
    member this.X = "F#"
