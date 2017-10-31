module CTrieTests
open Expecto
open CTrie
open FSharp.Collections.ParallelSeq

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
                Expect.isTrue (ctrie.Insert 1 1) "Inserting into an empty trie should succeed"
            }

            test "Inserting the same value twice should replace the existing value" {
                let ctrie = CTrie((=), hash)
                Expect.isTrue (ctrie.Insert 1 1) "First insert should succeed"
                Expect.isTrue (ctrie.Insert 1 2) "Second insert should succeed"
                Expect.equal (ctrie.Lookup 1) (Some 2) "Value should be found and be 2"
            }

            test "Inserting 1M ints should work" {
                let ctrie = CTrie((=), hash)
                Seq.init 100 id |> PSeq.iter (fun x -> ctrie.Insert x x |> ignore)
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