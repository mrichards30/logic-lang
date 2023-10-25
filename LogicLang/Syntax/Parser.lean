import LogicLang.Syntax.HandledType
import LogicLang.Syntax.Scanner

def delegate (input : List Token) : TokenParserContext α := {
    input := input
}

def error (token : Token) (error : String) (input : List Token) : TokenParserContext α := {
    input := input,
    errors := [(token, error)]
}

def assertOrderOfTokens (expected : List TokenType) (actual : List Token) : TokenParserContext Expression :=
    if expected.length == actual.length then
        let zip := expected.zip actual

        if zip.all (λ(type, token) => type == token.tokenType) then
            delegate actual

        else
            let failure := zip.find? (λ(type, token) => type != token.tokenType)

            match failure with
            | some (type, token) => error
                token s!"unexpected token `{token.lexeme}` at line {token.lineNumber} column {token.colNumber}; expected to see `{type}` here" actual
            | none => match actual.head? with
                | none => delegate actual
                | some h => error h "unexpected token" actual

    else
        match actual.head? with
            | none => delegate actual
            | some h => error h "mismatched comparison length" actual

def checkInjectiveFunctionDefinition (tokens : List Token) : TokenParserContext Expression :=
    match tokens with
    | injectiveKeyword :: fnKeyword :: functionName :: doubleColon :: domain :: arrow :: range :: semicolon ::_ =>
        if injectiveKeyword.tokenType != TokenType.Injective then delegate tokens
        else
            assertOrderOfTokens
                [TokenType.Injective, TokenType.Fn, TokenType.Identifier, TokenType.DoubleColon,
                    TokenType.Identifier, TokenType.RightArrow, TokenType.Identifier, TokenType.Semicolon]
                [injectiveKeyword, fnKeyword, functionName, doubleColon, domain, arrow, range, semicolon]

            ~> λ_ => pure (Expression.functionDefinition (some FnModifier.injective) functionName.lexeme domain.lexeme range.lexeme)
    | _ => delegate tokens

def checkFunctionDefinition (tokens : List Token) : TokenParserContext Expression :=
    match tokens with
    | fnKeyword :: functionName :: doubleColon :: domain :: arrow :: range :: semicolon ::_ => do
        if fnKeyword.tokenType != TokenType.Fn then delegate tokens

        else assertOrderOfTokens
                [TokenType.Fn, TokenType.Identifier, TokenType.DoubleColon, TokenType.Identifier,
                    TokenType.RightArrow, TokenType.Identifier, TokenType.Semicolon]
                [fnKeyword, functionName, doubleColon, domain, arrow, range, semicolon]

            ~> λ_ => pure (Expression.functionDefinition none functionName.lexeme domain.lexeme range.lexeme)
    | _ => delegate tokens

def checkEnumDefinition (tokens : List Token) : TokenParserContext Expression :=
    match tokens with
    | enumKeyword :: enumIdentifier :: equalsSign :: firstIdentifier :: xs => do
        unless enumKeyword.tokenType == TokenType.Enum do delegate tokens

        assertOrderOfTokens
            [TokenType.Enum, TokenType.Identifier, TokenType.Equals, TokenType.Identifier]
            [enumKeyword, enumIdentifier, equalsSign, firstIdentifier]

        ~> λ_ =>
            let remainder := xs.takeWhile (λtoken => token.tokenType != TokenType.Semicolon)
            let rec takeEnumValues (nextTokens : List Token) : Except String (List String) :=
                match nextTokens with
                | pipe :: identifier :: [] =>
                    if pipe.tokenType == TokenType.Pipe then Except.ok [identifier.lexeme]
                    else .error s!"expected a pipe '|' at line {pipe.lineNumber}, column {pipe.colNumber}."
                | pipe :: identifier :: xs =>
                    if pipe.tokenType != TokenType.Pipe then .error s!"expected a pipe '|' at line {pipe.lineNumber}, column {pipe.colNumber}."
                    else if identifier.tokenType != TokenType.Identifier then .error s!"expected an enum value at line {identifier.lineNumber}, column {identifier.colNumber}."
                    else
                        match takeEnumValues xs with
                        | Except.ok nextEnum => Except.ok (identifier.lexeme :: nextEnum)
                        | Except.error error => Except.error error
                | [] => Except.ok [firstIdentifier.lexeme]
                | _ => Except.error s!"bad enum definition on line {enumKeyword.lineNumber}; please use `enum Name = First | Second | Third;` and ensure a semicolon ends the line."

            match takeEnumValues remainder with
                | Except.ok subsequentEnumValues =>
                    let enumValues := firstIdentifier.lexeme :: subsequentEnumValues
                    return .enumDefinition enumIdentifier.lexeme enumValues
                | Except.error e => error enumKeyword e tokens

    | _ => delegate tokens

theorem takeWhile_cons : List.takeWhile f (x :: xs) = (match f x with
   | true => x :: List.takeWhile f xs
   | false => []) := rfl

theorem takeWhile_length_le : List.length (lst.takeWhile f) <= List.length lst := by
    induction lst with
    | nil => simp
    | cons x xs ih =>
        simp [takeWhile_cons]
        split
        simp_arith
        apply ih
        apply Nat.zero_le

theorem parseValue_termination (lst : List α) :
    List.length (List.takeWhile f value) < Nat.succ (Nat.succ (List.length value)) := by
        simp_arith [takeWhile_length_le]

def parseValue (tokens : List Token) : TokenParserContext Value :=
    match tokens with
        | fst :: snd :: value =>
            if fst.tokenType == TokenType.Identifier then

                if snd.tokenType == TokenType.RightParen || snd.tokenType == TokenType.Semicolon then
                    return Value.literal fst.lexeme

                else if snd.tokenType == TokenType.LeftParen then
                    let innerValue := value.takeWhile (λtoken => token.tokenType != TokenType.RightParen)
                    match parseValue innerValue with
                    | { result := some expr, .. } => return Value.functionCall fst.lexeme expr
                    | { result := none, errors := [], .. } => return Value.literal snd.lexeme
                    | current => current

                else
                    error fst s!"unexpected character `{snd.tokenType}` on line {snd.lineNumber}, column {snd.colNumber}" tokens
            else
                delegate tokens
        | [fst] => if fst.tokenType == TokenType.Identifier then return Value.literal fst.lexeme
                    else delegate tokens
        | _ => delegate tokens
    termination_by parseValue tokens => tokens.length
    decreasing_by apply parseValue_termination; assumption


def toComparisonOperation (token : Token) : Option ComparisonOperation :=
    match token.tokenType with
    | TokenType.Equals => some ComparisonOperation.equals
    | TokenType.NotEquals => some ComparisonOperation.notEquals
    | _ => none

def isComparisonOperator (token : Token) : Bool :=
    match toComparisonOperation token with
    | some _ => true
    | none => false

def findWithIndex? (f : α -> Bool) (lst : List α) : Option (α × Nat) :=
    let elementsAndIndex := lst.zip (List.range (lst.length - 1))
    let result? := elementsAndIndex.find? λ(e, _) => f e
    match result? with
        | some (e, i) => some (e, i)
        | none => none

def checkAssertionExpression (tokens : List Token) : TokenParserContext Expression :=
    let handle (tokens : List Token) : TokenParserContext Expression :=
        let comparator? := tokens.find? (λtoken => isComparisonOperator token)
        match comparator? with
        | some comparator =>

            let pre := tokens.takeWhile (λtoken => !isComparisonOperator token)
            let post := (tokens.reverse).takeWhile (λtoken => !isComparisonOperator token) |> List.reverse
            let op? := toComparisonOperation comparator

            match (parseValue pre, parseValue post, op?) with

                | ({ result := some x, .. }, { result := some y, .. }, some op) =>
                    return Expression.assertion (LogicalPredicate.predicate x op y)

                | ({ errors := es, .. }, { errors := mes, .. }, _) =>
                    { input := tokens, errors := es ++ mes }

        | none => delegate tokens

    let handleConnectedPredicate (operatorToken : Token) (index : Nat) (op : LogicalConnective) : TokenParserContext Expression :=

        let lhs := tokens.take index
        let rhs := (tokens.drop (index + 1))

        let syntaxError (side : String) := error operatorToken
            s!"syntax error on the {side} of the {op} operator; we expected to find a logical expression." tokens

        let leftExpr := if lhs.length < tokens.length then checkAssertionExpression lhs else syntaxError "left"
        let rightExpr := if rhs.length < tokens.length then checkAssertionExpression rhs else syntaxError "right"

        match (leftExpr, rightExpr) with
            | ({ result := Expression.assertion l, .. }, { result := Expression.assertion r, .. }) =>
                return Expression.assertion (LogicalPredicate.connect l op r)

            | ({ errors := leftErrors, .. }, { errors := rightErrors, .. }) =>
                { input := tokens, errors := leftErrors ++ rightErrors }

    let andOpWithIndex? := findWithIndex? (λtoken => token.tokenType == TokenType.And) tokens
    let orOpWithIndex? := findWithIndex? (λtoken => token.tokenType == TokenType.Or) tokens
    let implyOpWithIndex? := findWithIndex? (λtoken => token.tokenType == TokenType.RightArrow) tokens

    match (implyOpWithIndex?, andOpWithIndex?, orOpWithIndex?) with
        | (some (imply, index), _, _) => handleConnectedPredicate imply index LogicalConnective.implies -- and before or
        | (none, some (and, index), _) => handleConnectedPredicate and index LogicalConnective.and
        | (none, none, some (or, index)) => handleConnectedPredicate or index LogicalConnective.or -- and before or
        | (none, none, none) => handle tokens

    termination_by checkAssertionExpression xs => xs.length

def parseTokens (tokens : List Token) : Except String Expression :=

    if tokens.isEmpty then pure (Expression.expressions []) else

    let handledResult : TokenParserContext Expression :=
        checkFunctionDefinition tokens -- (~> is the chain of responsibility operator)
        ~> λnext => checkInjectiveFunctionDefinition next
        ~> λnext => checkEnumDefinition next
        ~> λnext => checkAssertionExpression next

    match (handledResult, tokens.head?) with
        | ({ result := some result, errors := [], .. }, _) => .ok result

        | ({ errors := [], .. }, some offender) =>
            if tokens.reverse.head?.map (λc => c.tokenType == TokenType.Semicolon) != some Bool.true
                then .error s!"error on line {offender.lineNumber}; expected semicolon at the end of the line but did not find one."
                else .error s!"error on line {offender.lineNumber}, column {offender.colNumber}; could not parse line beginning with keyword `{offender.lexeme}`. does it exist?"

        | ({ errors := [], .. }, none) =>
            .error s!"an unknown error occured; could not parse line."

        | ({ errors := errors, .. }, _) =>
            .error (errors |> toErrorMessage)

    where toErrorMessage (errors : List (Token × String)) :=
        errors.map (λ(t, e) => s!"error on line {t.lineNumber}, column {t.colNumber}: {e}")
        |> List.foldl (λnext (acc: String) => s!"{next}; {acc}") ""

def parseSingleLineString (input : String) (lineNumber : Nat) : Except String Expression := do
    let tokens <- scanTokens input lineNumber
    parseTokens tokens

def parseMultiLineString (input : String) : Except String Expression :=
    let lines := String.splitOn input "\n"
    let indexList := List.range lines.length
    let linesByIndex := lines.zip indexList
                        |> List.filter λ(s, _) => !s.trim.isEmpty
    aux linesByIndex

    where aux (tuples : List (String × Nat)) : Except String Expression :=
        match tuples with
            | (s, n) :: xs => do
                let rest <- aux xs
                let next <- parseSingleLineString s n
                .ok (next ++ rest)
            | [] => .ok (Expression.expressions [])

def horseQuestion := parseMultiLineString
        "
        enum Person = Matt | Liz | Joe | Kate;
        enum Horse = Morse | Lorse | Jorse | Korse;

        injective fn getHorse :: Person -> Horse;

        getHorse(Matt) = Morse ∨ getHorse(Matt) = Lorse;
        getHorse(Liz) = Morse ∨ getHorse(Liz) = Lorse;
        Korse = getHorse(Kate);
        getHorse(Joe) = getHorse(Liz);
        getHorse(Liz) = Lorse -> getHorse(Matt) = Morse;
        "
#eval horseQuestion
