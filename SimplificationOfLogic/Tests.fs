namespace SimplificationOfLogic
open System

module SimplificationTests =


// ------------------------------- Terms building for tests -------------------------------

    let a = Constant "a"
    let b = Constant "b"
    let c = Constant "c"
    let d = Constant "d"
    let e = Constant "e"
    let f = Constant "f"
    let g = Constant "g"
    let h = Constant "h"
    let i = Constant "i"

    let (!!) x = Terms.makeUnary OperationType.LogicalNeg x

    let (&&&) x y = Terms.makeNAry OperationType.LogicalAnd [x; y]

    let (|||) x y = Terms.makeNAry OperationType.LogicalOr [x; y]

    let (^) x y = Terms.makeNAry OperationType.LogicalXor [x; y]

    let (===) x y = Terms.makeNAry OperationType.Equal [x; y]

    let (-->) x y = !!x ||| y

// ----------------------------------- Tests -----------------------------------

    type testResult =
        { test : term; simplified : term; time : float }
        override x.ToString() =
            sprintf "Before simplification: %O\nAfter simplification: %O\nSimplification took: %O milliseconds" x.test x.simplified x.time

//  {Creating tests}

    let test1 = a &&& b &&& b &&& !!a &&& b &&& b
    let test2 = a &&& b &&& b &&& b &&& b
    let test3 = (a &&& b &&& c) &&& (!!a &&& b &&& !!c)
    let test4 = a ||| b ||| b ||| !!a ||| b ||| b
    let test5 = (a ||| b) ||| (a ||| b) ||| (a ||| b) ||| (a ||| b) ||| (a ||| b)
    let test6 = (a &&& b &&& c &&& d) ||| !!(a &&& b &&& c)
    let test7 = !!a &&& b ||| !!(a &&& b) ||| b
    let test8 = a &&& !!b ||| a &&& b &&& c ||| a &&& !!b &&& c ||| a &&& !!(b &&& c)
    let test9 = a &&& b &&& (!!a &&& c ||| !!(!!(a &&& b) &&& c) ||| c &&& d)
    let test10 = (a ||| b ||| !!c) &&& (a ||| !!b ||| !!c) &&& (!!a ||| b ||| c) &&& (!!a ||| b ||| !!c) &&& (!!a ||| !!b ||| !!c)
    let test11 = a ^ b ^ c ^ !!a
    let test12 = a ^ b ^ (b ^ a)
    let test13 = (!!a &&& b ||| !!c &&& b ||| (!!b ||| a) &&& (!!b ||| c)) &&& (!!a &&& b ||| !!c &&& b)
    let test14 = (a &&& b) ||| (!!a &&& f &&& !!h &&& !!i) ||| (!!a &&& g &&& !!h &&& !!i) ||| (b &&& e) ||| (b &&& !!f &&& !!g)
    let test15 = !!a &&& !!b &&& h ||| (!!h ||| a ||| b) &&& (!!a &&& !!b &&& c ||| (!!c ||| a ||| b) &&& (!!a &&& (!!a &&& ((!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& (!!b ||| !!d) ||| (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& b &&& d) &&& i ||| (!!i ||| a) &&& (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a))) &&& (!!b ||| !!d) &&& i ||| (!!i ||| a ||| b &&& d) &&& (!!a &&& ((!!a &&& ((!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& (!!b ||| !!d) ||| (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& b &&& d) &&& i ||| (!!i ||| a) &&& (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a))) &&& (!!b ||| !!d) ||| (!!a &&& ((!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& (!!b ||| !!d) ||| (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& b &&& d) &&& i ||| (!!i ||| a) &&& (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a))) &&& b &&& d) &&& e ||| (!!e ||| a) &&& (!!a &&& ((!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& (!!b ||| !!d) ||| (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a)) &&& b &&& d) &&& i ||| (!!i ||| a) &&& (!!a &&& !!b &&& c ||| (!!h ||| !!b ||| a) &&& (!!c ||| a))))))
    let test16 = (!!h ||| a ||| b) &&& (!!c &&& !!a &&& !!d &&& h &&& i &&& b ||| !!c &&& !!a &&& (!!i ||| b &&& d) &&& h &&& b) &&& (!!c ||| a ||| b)
    let test17 = (!!h ||| a ||| b) &&& (!!c ||| a ||| b) &&& (!!a &&& !!d &&& i &&& c &&& b ||| !!a &&& (!!i ||| b &&& d) &&& c &&& b)
    let test18 = !!a &&& !!b &&& h ||| (!!h ||| a ||| b) &&& (!!a &&& !!b &&& c ||| (!!c ||| a ||| b) &&& (!!a &&& (!!b ||| !!d) &&& i ||| (!!i ||| a ||| b &&& d) &&& (!!a &&& (!!i ||| !!b ||| !!d) &&& (!!b ||| !!d) &&& e ||| (!!i ||| !!b ||| !!d ||| a) &&& (!!e ||| a))))
    let test19 = !!c &&& !!a &&& !!b &&& (!!a &&& (!!b ||| !!d) &&& ((!!e ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& i ||| !!a &&& (!!b ||| !!d) &&& i &&& e) &&& h ||| !!c &&& !!a &&& !!b &&& ((!!i ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& ((!!e ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& h ||| !!c &&& !!a &&& !!b &&& ((!!i ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& h &&& e ||| !!a &&& !!b &&& (!!a &&& !!b &&& (!!a &&& (!!b ||| !!d) &&& ((!!e ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& i ||| !!a &&& (!!b ||| !!d) &&& i &&& e) &&& c ||| !!a &&& !!b &&& ((!!i ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& ((!!e ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& c ||| !!a &&& !!b &&& ((!!i ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& e &&& c) &&& h
    let test20 = (!!h ||| a ||| b) &&& (!!a &&& !!b &&& (!!a &&& (!!b ||| !!d) &&& ((!!e ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& i ||| !!a &&& (!!b ||| !!d) &&& i &&& e) &&& c ||| !!a &&& !!b &&& ((!!i ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& ((!!e ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& c ||| !!a &&& !!b &&& ((!!i ||| a) &&& (!!b ||| !!d) ||| b &&& d) &&& e &&& c)
    let test21 = !!a &&& !!b &&& c ||| (!!c ||| a ||| b) &&& (!!a &&& (!!a &&& ((!!c ||| !!b ||| a) &&& (!!b ||| !!d) ||| (!!c ||| a) &&& b &&& d) &&& e ||| (!!e ||| a) &&& (!!c ||| !!b ||| a)) &&& (!!b ||| !!d) &&& e ||| (!!e ||| a ||| b &&& d) &&& (!!a &&& ((!!a &&& ((!!c ||| !!b ||| a) &&& (!!b ||| !!d) ||| (!!c ||| a) &&& b &&& d) &&& e ||| (!!e ||| a) &&& (!!c ||| !!b ||| a)) &&& (!!b ||| !!d ||| !!f) ||| (!!a &&& ((!!c ||| !!b ||| a) &&& (!!b ||| !!d) ||| (!!c ||| a) &&& b &&& d) &&& e ||| (!!e ||| a) &&& (!!c ||| !!b ||| a)) &&& b &&& d &&& f) &&& g ||| (!!g ||| a) &&& (!!a &&& ((!!c ||| !!b ||| a) &&& (!!b ||| !!d) ||| (!!c ||| a) &&& b &&& d) &&& e ||| (!!e ||| a) &&& (!!c ||| !!b ||| a))))
    let test22 = !!a &&& !!b &&& c ||| (!!c ||| a ||| b) &&& (!!a &&& (!!b ||| !!d) &&& e ||| (!!e ||| a ||| b &&& d) &&& (!!a &&& ((!!e ||| !!b ||| !!d ||| a) &&& (!!b ||| !!d ||| !!f) ||| (!!e ||| a) &&& b &&& d &&& f) &&& g ||| (!!g ||| a) &&& (!!e ||| !!b ||| !!d ||| a)))
    let test23 = !!a &&& ((!!a &&& b ||| !!c &&& b) &&& (!!b ||| a) &&& (!!b ||| c) ||| (!!b ||| a) &&& (!!b ||| c)) &&& b
    let test24 = !!c &&& (!!a &&& b ||| !!c &&& b ||| (!!b ||| a) &&& (!!b ||| c)) &&& (!!a &&& b ||| !!c &&& b) &&& ((!!a &&& b ||| !!c &&& b) &&& (!!b ||| a) &&& (!!b ||| c) ||| (!!b ||| a) &&& (!!b ||| c)) &&& a &&& b
    let test25 = !!c &&& (!!a &&& b ||| !!c &&& b ||| (!!b ||| a) &&& (!!b ||| c)) &&& (!!a &&& b ||| !!c &&& b) &&& a &&& b
    let test26 = (!!a &&& b ||| !!c &&& b ||| (!!b ||| a) &&& (!!b ||| c)) &&& (!!a &&& b ||| !!c &&& b) &&& a &&& c &&& b
    let test27 = (!!a &&& b ||| !!c &&& b ||| (!!b ||| a) &&& (!!b ||| c)) &&& ((!!a &&& b ||| !!c &&& b) &&& (!!b ||| a) &&& (!!b ||| c) ||| (!!b ||| a) &&& (!!b ||| c))

    [<EntryPoint>]
    let main argv =
        assert(Array.length argv = 0)

        let allTests =
            [ test1; test2; test3; test4; test5; test6; test7; test8; test9; test10;
              test11; test12; test13; test14; test15; test16; test17; test18; test19; test20;
              test21; test22; test23; test24; test25; test26; test27 ]

//      {Simplifying tests}

        let simplify test =
            let stopWatch = System.Diagnostics.Stopwatch.StartNew()
            let simplified = simplifyPropTerm test
            stopWatch.Stop()
            { test = test; simplified = simplified; time = stopWatch.Elapsed.TotalMilliseconds }

        let simplifiedTests = List.map simplify allTests
        let printedTests = List.map toString simplifiedTests |> join "\n\n"
        Console.Write printedTests

        0
