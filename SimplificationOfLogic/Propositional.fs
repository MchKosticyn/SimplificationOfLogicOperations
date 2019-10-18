namespace SimplificationOfLogic

[<AutoOpen>]
module internal Propositional =

// ------------------------------- Utilities -------------------------------

    let makeBin operation x y =
        match x, y with
        | Expression(op', list'), Expression(op'', list'') when op' = operation && op'' = operation ->
            makeNAry operation (List.append list' list'')
        | Expression(_, []), _ -> y
        | _, Expression(_, []) -> y
        | Expression(op', list'), _ when op' = operation ->
            makeNAry operation (y::list')
        | _, Expression(op', list') when op' = operation ->
            makeNAry operation (x::list')
        | _ -> makeNAry operation [x; y]

    let private makeCoOpBinaryTerm x list listOp op =
        match list with
        | [] -> x
        | [y] -> makeBin op x y
        | _ -> makeBin op (Expression(listOp, list)) x

    let private (|IntersectionExceptOneNegation|_|) (list1 : term list) (list2 : term list) =
        let s1 = System.Collections.Generic.HashSet<term>(list1)
        let s2 = System.Collections.Generic.HashSet<term>(list2)
        let intersection = list2 |> Seq.fold (fun acc x -> if s1.Remove(x) then s2.Remove(x) |> ignore; x::acc else acc) []
        if s1.Count <> 1 then None
        else
            match Seq.head s1 with
            | Negation y as x when s2.RemoveWhere(System.Predicate<term>((=)y)) > 0 -> Some(x, intersection, List.ofSeq s2)
            | x when s2.RemoveWhere(System.Predicate<term>(function | Negation y when x = y -> true | _ -> false)) > 0 -> Some(x, intersection, List.ofSeq s2)
            | _ -> None

    let private isPermutationOf list1 list2 =
        if List.length list1 <> List.length list2 then false
        else
            let s1 = System.Collections.Generic.HashSet<term>(list1)
            let s2 = System.Collections.Generic.HashSet<term>(list2)
            s1.SymmetricExceptWith(s2); Seq.isEmpty s1

// ------------------------------- Simplification of logical operations -------------------------------

    // Trying to simplify pairwise combinations of x- and y-operands.
    // For example, it tries to simplify (a + b) + (c + d) or (a * b) * (c * d)
    // by successively trying to combine (a * c), (a * d), (b * c) and (b * d).
    let simplifyPairwiseCombinations xs ys simplify reduce matched unmatched =
        let initialYs = ys

        let rec combineOne x ys failed k =
            match ys with
            | [] -> k x failed
            | h :: tl ->
                simplify x h
                    (fun x -> combineOne x tl failed k)
                    (fun () -> combineOne x tl (h::failed) k)

        let rec combine xs ys acc =
            match xs with
            | [] ->
                // Here we traversed all xs, checking for something matched...
                if List.length ys = List.length initialYs then unmatched () // Nothing matched, the whole process is failed
                else
                    // Something matched, the work is done, just combining results together...
                    let toReduce = List.append (List.rev acc) ys
                    Cps.List.reducek reduce toReduce matched
            | x::xs ->
                combineOne x ys [] (fun res ys -> combine xs ys (res::acc))

        combine xs ys []

    let rec private simplifyConnective operation opposite stopValue ignoreValue x y k =
        let defaultCase () = makeBin operation x y |> k
        simplifyExt operation opposite stopValue ignoreValue x y k defaultCase

    and private simplifyExt op co stopValue ignoreValue x y matched unmatched =
        match x, y with
        | _ when y = ignoreValue -> matched x
        | _ when x = ignoreValue -> matched y
        | _ when y = stopValue -> matched stopValue
        | _ when x = stopValue -> matched stopValue
        | _ when x = y -> matched x
        | Negation x, _ when x = y -> matched stopValue
        | _, Negation y when x = y -> matched stopValue
        | Expression _, Expression _ ->
            simplifyExpression op co stopValue ignoreValue x y matched (fun () ->
            simplifyExpression op co stopValue ignoreValue y x matched unmatched)
        | Expression _, _ -> simplifyOpToExpr x y op co stopValue ignoreValue matched unmatched
        | _, Expression _ -> simplifyOpToExpr y x op co stopValue ignoreValue matched unmatched
        | _ -> unmatched ()

    and private simplifyExpression op co stopValue ignoreValue x y matched unmatched =
        match x with
        | Expression(op', list) when op = op'->
            simplifyOpOp op co stopValue ignoreValue list y matched unmatched
        | Expression(co', list) when co = co'->
            simplifyCoOp op co stopValue ignoreValue x list y matched unmatched
        | _ -> unmatched ()

    and simplifyOpOp op co stopValue ignoreValue xargs y matched unmatched =
        // simplifying (OP list) op y at this step
        match xargs, y with
        | [x], y -> simplifyExt op co stopValue ignoreValue x y matched unmatched
        | _ ->
            // Trying to simplify pairwise combinations of x- and y-summands
            let yargs =
                match y with
                | Expression(op', y') when op = op'-> y'
                | _ -> [y]
            simplifyPairwiseCombinations xargs yargs (simplifyExtWithType op co stopValue ignoreValue) (simplifyConnective op co stopValue ignoreValue) matched unmatched

    and simplifyCoOp op co stopValue ignoreValue x list y matched unmatched =
        match list, y with
        | [x], _ -> simplifyExt op co stopValue ignoreValue x y matched unmatched
        // Co(... y ...) op y = y
        | _ when List.contains y list -> matched y
        // Co(... y ...) op !y = Co(... ...) op !y
        | _, Negation y' when List.contains y' list -> matched (makeCoOpBinaryTerm y (List.except [y'] list) co op)
        // Co(... !y ...) op y = Co(... ...) op y
        | _ when List.contains (negate y) list -> matched (makeCoOpBinaryTerm y (List.except [negate y] list) co op)
        // Co(!a ys) op Co(a ys) = ys
        // Co(a ys) op Co(!a ys zs) = ys co (a op Co(zs)) if (a op Co(zs)) simplifies
        // Co(a ys) op Co(!a ys zs) = Co(a ys) op Co(ys zs)
        | _, Expression(co', IntersectionExceptOneNegation list (a, ys, zs)) when co' = co ->
            if zs.IsEmpty then makeNAry co ys |> matched
            else
                let coZs = makeNAry co zs
                simplifyExt op co stopValue ignoreValue a coZs
                    (fun aOpZs -> makeNAry co (aOpZs::ys) |> matched)
                    (fun () ->
                        let y' = makeNAry co (List.append ys zs)
                        simplifyCoOp op co stopValue ignoreValue x list y' matched (fun () ->
                        makeNAry op [x; y'] |> matched))
        // Co(list) op Co(permutation of list) -> Co(list)
        | _, Expression(co', ys)  when co' = co && isPermutationOf list ys -> matched x
        // Co(...) op OP(...) -> pairwise
        | _, Expression(op', y') when op = op' ->
            // Trying to simplify pairwise combinations of x- and y-summands
            simplifyPairwiseCombinations [x] y' (simplifyExtWithType op co stopValue ignoreValue) (simplifyConnective op co stopValue ignoreValue) matched unmatched
        | _ -> unmatched ()

    and private simplifyOpToExpr x y op co stopValue ignoreValue matched unmatched =
        match x with
        | Expression(op', xs) when op = op'->
            simplifyOpOp op co stopValue ignoreValue xs y matched unmatched
        | Expression(op', xs) when co = op'->
            simplifyCoOp op co stopValue ignoreValue x xs y matched unmatched
        | _ -> unmatched ()

    and simplifyAnd x y k =
        simplifyConnective OperationType.LogicalAnd OperationType.LogicalOr False True x y k

    and simplifyOr x y k =
        simplifyConnective OperationType.LogicalOr OperationType.LogicalAnd True False x y k

    and simplifyNegation x k =
        match x with
        | Concrete b -> Concrete (not (b :?> bool)) |> k
        | Negation x -> k x
        | Conjunction xs -> Cps.List.mapk simplifyNegation xs (makeNAry OperationType.LogicalOr >> k)
        | Disjunction xs -> Cps.List.mapk simplifyNegation xs (makeNAry OperationType.LogicalAnd >> k)
        | _ -> makeUnary OperationType.LogicalNeg x |> k

    and private simplifyExtWithType op co stopValue ignoreValue x y matched unmatched =
        simplifyExt op co stopValue ignoreValue x y matched unmatched

// ------------------------------- General functions -------------------------------

    let private (!!) x = simplifyNegation x id

    let private (&&&) x y = simplifyAnd x y id

    let private (|||) x y = simplifyOr x y id

    let simplifyBinaryConnective op x y k =
        match op with
        | OperationType.LogicalAnd -> simplifyAnd x y k
        | OperationType.LogicalOr -> simplifyOr x y k
        | OperationType.LogicalXor ->
            simplifyNegation x (fun x' ->
            simplifyNegation y (fun y' ->
            simplifyOr x' y' (fun x' ->
            simplifyOr x y (fun y' ->
            simplifyAnd x' y' k))))
        | OperationType.Equal ->
            simplifyNegation x (fun x' ->
            simplifyOr x' y (fun x' ->
            simplifyNegation y (fun y' ->
            simplifyOr x y' (fun y' ->
            simplifyAnd x' y' k))))
        | OperationType.NotEqual ->
            simplifyNegation x (fun x' ->
            simplifyOr x' y (fun x' ->
            simplifyNegation y (fun y' ->
            simplifyOr x y' (fun y' ->
            simplifyAnd x' y' (fun res ->
            simplifyNegation res k)))))
        | _ -> internalfailf "%O is not a binary logical operator" op

    let simplifyUnaryConnective op x k =
        match op with
        | OperationType.LogicalNeg -> simplifyNegation x k
        | _ -> internalfailf "%O is not an unary logical operator" op

    let simplifyOperation op args k =
        let arity = Operations.operationArity op
        match arity with
        | 1 ->
            assert(List.length args = 1)
            simplifyUnaryConnective op (List.head args) k
        | 2 ->
            assert(List.length args >= 2)
            Cps.List.reducek (fun x y k -> simplifyBinaryConnective op x y k) args k
        | _ -> internalfailf "unknown operation %O" op

    let simplifyPropTerm term =
        match term with
        | Concrete _
        | Constant _ -> term
        | Expression(op, args) -> simplifyOperation op args id
