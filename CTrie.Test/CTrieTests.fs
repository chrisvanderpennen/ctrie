module CTrieTests
open Expecto
open CTrie

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
        ]
    ]