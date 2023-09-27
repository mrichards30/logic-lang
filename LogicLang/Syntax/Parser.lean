import LogicLang.Syntax.HandledType
import LogicLang.Syntax.Scanner

abbrev ParseResult := HandledResult String Expression (List Token)

def assertOrderOfTokens (expected : List TokenType) (actual : List Token) : ParseResult := 
    if expected.length == actual.length then
        let zip := expected.zip actual
        if zip.all (λ(type, token) => type == token.tokenType) then
            HandledResult.delegate actual
        else 
            let failure := zip.find? (λ(type, token) => type != token.tokenType)
            match failure with 
            | some (type, token) => HandledResult.failed 
                s!"unexpected token `{token.lexeme}` at line {token.lineNumber} column {token.colNumber}; expected to see `{type}` here" 
            | none => HandledResult.failed "unexpected token " 
    else HandledResult.failed "mismatched comparison length"

def checkInjectiveFunctionDefinition (tokens : List Token) : ParseResult := 
    match tokens with
    | injectiveKeyword :: fnKeyword :: functionName :: doubleColon :: domain :: arrow :: range :: semicolon ::_ => do
        unless injectiveKeyword.tokenType == TokenType.Injective do return tokens
        let _ <- assertOrderOfTokens 
            [TokenType.Injective, TokenType.Fn, TokenType.Identifier, TokenType.DoubleColon, 
                TokenType.Identifier, TokenType.RightArrow, TokenType.Identifier, TokenType.Semicolon]
            [injectiveKeyword, fnKeyword, functionName, doubleColon, domain, arrow, range, semicolon]
        HandledResult.handled 
            (Expression.functionDefinition (some FnModifier.injective) functionName.lexeme domain.lexeme range.lexeme)
    | _ => HandledResult.delegate tokens

def checkFunctionDefinition (tokens : List Token) : ParseResult := 
    match tokens with
    | fnKeyword :: functionName :: doubleColon :: domain :: arrow :: range :: semicolon ::_ => do
        unless fnKeyword.tokenType == TokenType.Fn do return tokens
        let _ <- assertOrderOfTokens 
                [TokenType.Fn, TokenType.Identifier, TokenType.DoubleColon, TokenType.Identifier, 
                    TokenType.RightArrow, TokenType.Identifier, TokenType.Semicolon]
                [fnKeyword, functionName, doubleColon, domain, arrow, range, semicolon]
        HandledResult.handled 
            (Expression.functionDefinition none functionName.lexeme domain.lexeme range.lexeme)
    | _ => HandledResult.delegate tokens

def checkEnumDefinition (tokens : List Token) : ParseResult :=
    match tokens with 
    | enumKeyword :: enumIdentifier :: equalsSign :: firstIdentifier :: xs => do 
        unless enumKeyword.tokenType == TokenType.Enum do return tokens
        let _ <- assertOrderOfTokens 
                    [TokenType.Enum, TokenType.Identifier, TokenType.Equals, TokenType.Identifier]
                    [enumKeyword, enumIdentifier, equalsSign, firstIdentifier] 

        let remainder := xs.takeWhile (λtoken => token.tokenType != TokenType.Semicolon)
        let rec takeEnumValues (nextTokens : List Token) : Except String (List String) := 
            match nextTokens with 
            | pipe :: identifier :: [] => 
                if pipe.tokenType == TokenType.Pipe then Except.ok [identifier.lexeme] 
                else Except.error "expected pipe; did not find one"
            | pipe :: identifier :: xs => 
                match takeEnumValues xs with 
                | Except.ok nextEnum => Except.ok (identifier.lexeme :: nextEnum)
                | Except.error error => Except.error error
            | [] => Except.ok [firstIdentifier.lexeme]
            | _ => Except.error s!"bad enum definition on line {enumKeyword.lineNumber}; please use `enum Name = First | Second | Third;` and ensure a semicolon ends the line."
        
        match takeEnumValues remainder with 
        | Except.ok subsequentEnumValues => 
            let enumValues := firstIdentifier.lexeme :: subsequentEnumValues
            HandledResult.handled (Expression.enumDefinition enumIdentifier.lexeme enumValues) 
        | Except.error e => HandledResult.failed e 

    | _ => HandledResult.delegate tokens

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
        
def parseValue (tokens : List Token) : HandledResult String Value (List Token) := 
    match tokens with 
        | fst :: snd :: value =>
            if fst.tokenType == TokenType.Identifier then
            
                if snd.tokenType == TokenType.RightParen || snd.tokenType == TokenType.Semicolon then
                    .handled (Value.literal fst.lexeme)
                    
                else if snd.tokenType == TokenType.LeftParen then
                    let innerValue := value.takeWhile (λtoken => token.tokenType != TokenType.RightParen)
                    match parseValue innerValue with 
                    | .handled expr => .handled (Value.functionCall fst.lexeme expr)
                    | .failed e => .failed e 
                    | .delegate _ => .handled (Value.literal snd.lexeme)

                else 
                    .failed s!"unexpected character `{snd.tokenType}` on line {snd.lineNumber}, column {snd.colNumber}"
            else 
                .delegate tokens
        | [fst] => if fst.tokenType == TokenType.Identifier then .handled (Value.literal fst.lexeme)
                    else .delegate tokens
        | _ => .delegate tokens
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

def findIndex? (f : α -> Bool) (lst : List α) : Option Nat := 
    let elementsAndIndex := lst.zip (List.range (lst.length - 1))
    let result? := elementsAndIndex.find? λ(e, _) => f e
    match result? with 
        | some (_, i) => some i
        | none => none 

def checkAssertionExpression (tokens : List Token) : ParseResult := 
    let handle (tokens : List Token) : ParseResult := 
        let comparator? := tokens.find? (λtoken => isComparisonOperator token)
        match comparator? with 
        | some comparator => 
            let pre := tokens.takeWhile (λtoken => !isComparisonOperator token)
            let post := (tokens.reverse).takeWhile (λtoken => !isComparisonOperator token) |> List.reverse
            let op? := toComparisonOperation comparator

            match (parseValue pre, parseValue post, op?) with
            | (.handled x, .handled y, some op) => 
                .handled (Expression.assertion (LogicalPredicate.predicate x op y))
            | (.failed e1, .failed e2, _) => .failed (e1 ++ "; also, " ++ e2)
            | (.failed e, _, _) => .failed e
            | (_, .failed e, _) => .failed e
            | (_, _, _) => .delegate tokens

        | none => .delegate tokens

    let handleConnectedPredicate (index : Nat) (op : LogicalConnective) : ParseResult := 

        let lhs := tokens.take index
        let rhs := (tokens.drop (index + 1)) 

        let syntaxError (side : String) := HandledResult.failed 
            s!"syntax error on the {side} of the {op} operator; we expected to find a logical expression."

        let leftExpr := if lhs.length < tokens.length then checkAssertionExpression lhs else syntaxError "left"
        let rightExpr := if rhs.length < tokens.length then checkAssertionExpression rhs else syntaxError "right"

        match (leftExpr, rightExpr) with
            | (HandledResult.handled (Expression.assertion l), HandledResult.handled (Expression.assertion r)) => .handled (Expression.assertion (LogicalPredicate.connect (l) op r))
            | (HandledResult.failed e1, HandledResult.failed e2) => .failed (e1 ++ "; also " ++ e2)
            | (HandledResult.failed e, _) => .failed e
            | (_, HandledResult.failed e) => .failed e
            | (_, _) => .failed "incorrect type of expression in connected logical statement. only assertions can be used here."
        
    let andIndex? := findIndex? (λtoken => token.tokenType == TokenType.And) tokens
    let orIndex? := findIndex? (λtoken => token.tokenType == TokenType.Or) tokens
    match (andIndex?, orIndex?) with
        | (some index, _) => handleConnectedPredicate index LogicalConnective.and
        | (none, some index) => handleConnectedPredicate index LogicalConnective.or -- and before or 
        | (none, none) => handle tokens
    termination_by checkAssertionExpression xs => xs.length 

def parseTokens (tokens : List Token) : Except String Expression := 
    let handledResult : ParseResult := do
        let next <- checkFunctionDefinition tokens
        let next <- checkInjectiveFunctionDefinition next
        let next <- checkEnumDefinition next
        checkAssertionExpression next

    match handledResult with 
        | HandledResult.delegate _ => .error "could not interpret line; no rule matched what was typed"
        | HandledResult.failed x => .error x
        | HandledResult.handled x => .ok x 

def parseSingleLineString (input : String) (lineNumber : Nat) : Except String Expression := do
    let tokens <- scanTokens input lineNumber
    parseTokens tokens 

def parseMultiLineString (input : String) : Except String (List Expression) :=
    let lines := String.splitOn input "\n"
    let indexList := List.range lines.length
    let linesByIndex := lines.zip indexList 
                        |> List.filter λ(s, _) => !s.trim.isEmpty
    aux linesByIndex

    where aux (tuples : List (String × Nat)) : Except String (List Expression) :=
        match tuples with
            | (s, n) :: xs => do
                let rest <- aux xs
                let next <- parseSingleLineString s n
                .ok (next :: rest)
            | [] => .ok []

def horseQuestion := parseMultiLineString 
        "
        enum Equestrian = Mountback | Hacking | Klamberon | Topalov;
        enum Horse = Bay | Black | Chestnut | Gray;
        enum Activity = StandingStill | Jumping | Trotting | GallopingWithMountback;

        injective fn getActivity :: Horse -> Activity;
        injective fn getHorse :: Equestrian -> Horse; 

        getHorse(Hacking) = Bay ∨ getActivity(Mountback) = Bay; 
        getActivity(getHorse(Klamberon)) != Jumping;
        getActivity(Gray) != Trotting;
        getHorse(Topalov) = Chestnut;
        "
#eval horseQuestion
