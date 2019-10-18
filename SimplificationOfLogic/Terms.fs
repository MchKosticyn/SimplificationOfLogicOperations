namespace SimplificationOfLogic

open System

[<StructuralEquality;NoComparison>]
type term =
    | Concrete of obj
    | Constant of string
    | Expression of OperationType * term list

    override x.ToString() =

        let addBracketsIfNeed parentPriority priority str = if priority < parentPriority then sprintf "(%s)" str else str

        let rec toStr parentPriority term =
            match term with
            | Constant name -> name
            | Concrete value -> value.ToString()
            | Expression(operation, operands) ->
                let priority = Operations.operationPriority operation
                match operation with
                | _ when Operations.isUnary operation ->
                    assert (List.length operands = 1)
                    let operand = List.head operands
                    let opStr = Operations.operationToString operation
                    let printedOperand = toStr priority operand
                    opStr + printedOperand |> addBracketsIfNeed parentPriority priority
                | _ ->
                    assert (List.length operands >= 2)
                    let printedOperands = operands |> List.map (toStr priority)
                    let sortedOperands = if Operations.isCommutative operation then List.sort printedOperands else printedOperands
                    sortedOperands
                        |> String.concat (Operations.operationToString operation)
                        |> addBracketsIfNeed parentPriority priority

        toStr -1 x

[<AutoOpen>]
module internal Terms =

// --------------------------------------- Primitives ---------------------------------------

    let isConcrete = function
        | Concrete _ -> true
        | _ -> false

    let isExpression = function
        | Expression _ -> true
        | _ -> false

    let isTrue = function
        | Concrete b when (b :?> bool) -> true
        | _ -> false

    let isFalse = function
        | Concrete b when not (b :?> bool) -> true
        | _ -> false

    let operationOf = function
        | Expression(op, _) -> op
        | term -> internalfailf "expression expected, %O received" term

    let argumentsOf = function
        | Expression(_, args) -> args
        | term -> internalfailf "expression expected, %O received" term

    let True = Concrete(box true)
    let False = Concrete(box false)

    let makeBool predicate =
        if predicate then True else False

    let makeNAry operation x =
        match x with
        | [] -> raise(new ArgumentException("List of args should be not empty"))
        | [x] -> x
        | _ -> Expression(operation, x)

    let makeUnary operation x =
        assert(Operations.isUnary operation)
        Expression(operation, [x])

    let negate term = makeUnary OperationType.LogicalNeg term

    let (|True|_|) term = if isTrue term then Some True else None
    let (|False|_|) term = if isFalse term then Some False else None

    let (|Negation|_|) = function
        | Expression(OperationType.LogicalNeg, [x]) -> Some(Negation x)
        | _ -> None

    let (|Conjunction|_|) = function
        | Expression(OperationType.LogicalAnd, xs) -> Some(Conjunction xs)
        | _ -> None

    let (|Disjunction|_|) = function
        | Expression(OperationType.LogicalOr, xs) -> Some(Disjunction xs)
        | _ -> None

    let (|Xor|_|) = function
        | Expression(OperationType.LogicalXor, [x;y]) -> Some(Xor(x, y))
        | _ -> None
