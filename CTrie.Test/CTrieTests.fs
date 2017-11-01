module CTrieTests
open Expecto
open CTrie
open FSharp.Collections.ParallelSeq
open System.Collections.Concurrent

type ZeroHashCode(i: int)  =
    override x.Equals(other) =
        match other with
            | :? ZeroHashCode as c -> c.Value = x.Value
            | _ -> false

    override x.GetHashCode () = 0
    member this.Value = i

[<Tests>]
let tests =
    testList "CTrie tests" [
        testList "Insert" [
            test "Inserting into an empty trie should succeed" {
                let ctrie = CTrie((=), hash)
                Expect.isTrue (ctrie.Insert 0 0) "Inserting into an empty trie should succeed"
            }

            test "Inserting the same value twice should replace the existing value" {
                let ctrie = CTrie((=), hash)
                Expect.isTrue (ctrie.Insert 1 1) "First insert should succeed"
                Expect.isTrue (ctrie.Insert 1 2) "Second insert should succeed"
                Expect.equal (ctrie.Lookup 1) (Some 2) "Value should be found and be 2"
            }

            test "Inserting 1M ints should work" {
                let ctrie = CTrie((=), hash)
                let ins x = ctrie.Insert x x |> ignore
                let rem x = ctrie.Remove x
                
                let count = 1000000

                PSeq.init count id |> PSeq.iter ins
                Expect.equal (Seq.length (ctrie.DebugSeq ())) count "didn't iterate enough items"
                let lookups = PSeq.init count id |> PSeq.map ctrie.Lookup
                Expect.hasCountOf lookups (uint32 count) Option.isSome "didn't lookup enough items"
                let removed = PSeq.init count id |> PSeq.map rem |> PSeq.toList
                Expect.hasCountOf removed (uint32 count) Option.isSome  "didn't remove enough items"
            }

            test "Faster than ConcurrentDictionary" {
                let count = 1000000
                let trieInsert () = 
                    let ctrie = CTrie((=), hash)
                    let ins x = ctrie.Insert x x |> ignore
                    PSeq.init count id |> PSeq.iter ins
                let dictInsert () =
                    let cdict = ConcurrentDictionary<int, int>()
                    let cins x = cdict.TryAdd(x,x) |> ignore
                    PSeq.init count id |> PSeq.iter cins

                Expect.isFasterThan trieInsert dictInsert "trie should be faster"
            }

            test "Hash collisions" {
                let ctrie = CTrie((=), hash)
                Expect.isTrue (ctrie.Insert (ZeroHashCode(1)) 1) "First insert should succeed"
                Expect.isTrue (ctrie.Insert (ZeroHashCode(2)) 2) "Second insert should succeed"
                Expect.equal (ctrie.Lookup (ZeroHashCode(1))) (Some 1) "Collision of 1 should be 1"
                Expect.equal (ctrie.Lookup (ZeroHashCode(2))) (Some 2) "Collision of 2 should be 2"
                Expect.equal (ctrie.Lookup (ZeroHashCode(3))) None "Collision of 3 should not be present"
            }
        ]
    ]