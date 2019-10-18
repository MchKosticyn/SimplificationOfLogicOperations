namespace SimplificationOfLogic

type OperationType =
    | LogicalNeg = 0
    | LogicalAnd = 1
    | LogicalOr = 2
    | LogicalXor = 3
    | Equal = 4
    | NotEqual = 5

module internal Operations =

    let operationArity = function
        | OperationType.LogicalNeg -> 1
        | _ -> 2
    let isUnary op = operationArity op = 1
    let isBinary op = operationArity op = 2

    let maxPriority = 10
    let operationPriority = function
        | OperationType.LogicalNeg -> maxPriority
        | OperationType.Equal
        | OperationType.NotEqual -> maxPriority - 5
        | OperationType.LogicalAnd -> maxPriority - 6
        | OperationType.LogicalXor -> maxPriority - 7
        | OperationType.LogicalOr -> maxPriority - 8
        | _ -> -1

    let isCommutative = function
        | OperationType.Equal
        | OperationType.LogicalAnd
        | OperationType.LogicalOr
        | OperationType.LogicalXor -> true
        | _ -> false

    let operationToString = function
        | OperationType.Equal -> " == "
        | OperationType.NotEqual -> " != "
        | OperationType.LogicalAnd -> " & "
        | OperationType.LogicalOr -> " | "
        | OperationType.LogicalNeg -> "!"
        | OperationType.LogicalXor -> " ^ "
        | _ -> ""
