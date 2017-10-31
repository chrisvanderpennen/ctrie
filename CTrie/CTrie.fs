namespace CTrie
open System.Threading

[<NoEquality;NoComparison>]
type internal SNode<'k,'v> = ('k * 'v)

type internal TNode<'k,'v> = {sn: SNode<'k,'v>; mutable prev: MainNode<'k,'v> option}

and internal CNode<'k,'v> = {bitmap: int; array: Branch<'k,'v>[]; mutable prev: MainNode<'k,'v> option} with
    member this.insertAt flag pos node =
        let arr = Array.zeroCreate (this.array.Length + 1)
        Array.blit this.array 0 arr 0 pos
        Array.set arr pos node
        Array.blit this.array pos arr (pos + 1) (this.array.Length - pos)
        {this with bitmap=this.bitmap|||flag; array=arr;}
    member this.updateAt pos node =
        let arr = Array.copy this.array
        Array.set arr pos node
        {this with array=arr}
    member this.removeAt flag pos =
        let arr = Array.zeroCreate (this.array.Length - 1)
        Array.blit this.array 0 arr 0 pos
        Array.blit this.array (pos+1) arr pos (this.array.Length - pos - 1)
        {this with bitmap=this.bitmap^^^flag}

and internal LNode<'k,'v> = {list: SNode<'k,'v> list; mutable prev: MainNode<'k,'v> option}

and internal INode<'k,'v> = {mutable main: MainNode<'k,'v>; generation: obj;} with
    member this.ReadMain () =
        Volatile.Read &this.main

    member this.TryUpdate currentMain newMain =
        LanguagePrimitives.PhysicalEquality 
            currentMain 
            (Interlocked.CompareExchange(&this.main,newMain,currentMain))

and internal MainNode<'k,'v> =
    | CN of CNode<'k,'v>
    | TN of TNode<'k,'v>
    | LN of LNode<'k,'v>
    | Failed of MainNode<'k,'v> option
    member this.Prev
        with get () = match this with Failed f -> f | LN n -> Volatile.Read &n.prev | CN n -> Volatile.Read &n.prev | TN n -> Volatile.Read &n.prev
        and set v = match this with Failed _ -> () | LN n -> Volatile.Write(&n.prev, v) | CN n -> Volatile.Write(&n.prev, v) | TN n -> Volatile.Write(&n.prev, v)

and internal Branch<'k,'v> =
    | IN of INode<'k,'v>
    | SN of SNode<'k,'v>

module CTrie =
    [<Literal>] 
    let private BitmapLength = 5
    
    type Result<'v> =
        Restart
        | Result of 'v option

    let private bitcount i =
        let mutable i = i
        i <- (i >>> 1) &&& 0x55555555
        i <- (i &&& 0x33333333) + ((i >>> 2) &&& 0x33333333)
        (((i + (i >>> 4)) &&& 0x0f0f0f0f) * 0x01010101) >>> 24
    
    let inline private flagpos hc bmp lev =
        let index = (hc >>> lev) &&& 0x1f
        let flag = 1 <<< index
        let pos = bitcount (bmp &&& (flag - 1))
        flag, pos
    
    let private flagUnset i bmp =
        i &&& bmp = 0

    let private resurrect n =
        match n with
            | IN i -> match i.ReadMain () with
                            | TN tn -> SN tn.sn
                            | _ -> IN i
            | SN _ -> n

    let rec private createCNode hashcode a b level gen =
        if level > 32 then
            LN {list=[a;b]; prev=None}
        else
            let mutable array = Array.empty
            let aflag, apos = flagpos (hashcode (fst a)) 0 level
            let bitmap, bpos = flagpos (hashcode (fst b)) aflag level
            if apos = bpos then
                let inode = IN {main=createCNode hashcode a b (level+BitmapLength) gen; generation=gen}
                array <- [| inode |]
            else if apos > bpos then
                array <- [| (SN b); (SN a) |]
            else
                array <- [| (SN a); (SN b) |]
            CN { array=array; bitmap=bitmap; prev=None }

    let private toContracted cnode level =
        if level > 0 && cnode.array.Length = 1 then
            match cnode.array.[0] with
                | SN sn -> TN { sn = sn; prev=None; }
                | _ -> CN cnode
        else CN cnode
    let private toCompressed cn level =
        let newCNode = { bitmap = cn.bitmap; array = Array.map resurrect cn.array; prev=None }
        toContracted newCNode level

    let private clean (inode: INode<'a,'b> option) level =
        match inode with
            | Some node -> 
                let m = node.ReadMain ()
                match m with
                    | CN cn -> ignore(node.TryUpdate m (toCompressed cn level))
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
            | LN ln -> Result (List.tryFind (fst >> equals key) ln.list |> Option.bind (snd >> Some))

    let rec internal iinsert equals hashCode (inode: INode<'a,'b>) key value level parent generation =
        let n = inode.ReadMain ()
        match n with
            | CN cn ->
                let flag, pos = flagpos (hashCode key) cn.bitmap level
                if flagUnset flag cn.bitmap then
                    let ncn = cn.insertAt flag pos (SN (key, value))
                    inode.TryUpdate n (CN ncn)
                else
                    match cn.array.[pos] with
                        | IN _ -> iinsert equals hashCode inode key value (level + BitmapLength) (Some inode) generation
                        | SN sn ->
                            if not(equals key (fst sn)) then
                                let nin = IN {main=createCNode hashCode sn (key, value) (level + BitmapLength) generation; generation=generation}
                                let ncn = cn.updateAt pos nin
                                inode.TryUpdate n (CN ncn)
                            else
                                let ncn = cn.updateAt pos (SN (key, value))
                                inode.TryUpdate n (CN ncn)
            | TN _ -> clean parent (level - BitmapLength); false
            | LN ln -> inode.TryUpdate n (LN {ln with list=(key, value) :: ln.list})

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
                                let ncn = cn.removeAt flag pos 
                                let cntr = toContracted ncn lev
                                if i.TryUpdate n cntr then Result (Some (snd sn))
                                else Restart
                            else Result None
            | TN _ -> clean parent (lev - BitmapLength); Restart
            | LN ln ->
                let nln = List.filter (fst >> eq) ln.list
                let result = ln.list |> (List.tryFind (fst >> eq) >> function | Some x -> Some (snd x) | None -> None)
                if nln.Length = 1 then
                    if i.TryUpdate n (TN {sn=nln.Head; prev=None;}) then Result result else Restart
                else if i.TryUpdate n (LN {ln with list=nln}) then Result result else Restart

open CTrie
open System.Collections.Generic
type CTrie<'k,'v>(equals, hashCode, readonly) =
    let equals = equals
    let hashCode = hashCode
    let mutable generation = new obj ()
    
    [<VolatileField>]
    let mutable root: INode<'k,'v> = {main=CN { bitmap=0; array=Array.empty; prev=None }; generation=generation}

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
    new(comparer: IEqualityComparer<'k>) = CTrie((fun x y -> comparer.Equals(x,y)), comparer.GetHashCode)
