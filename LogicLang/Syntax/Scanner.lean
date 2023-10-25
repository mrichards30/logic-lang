import LogicLang.Proof.Lemmas
import LogicLang.Syntax.Expressions

inductive TokenType where
    -- single-character symbols
    | LeftParen
    | RightParen
    | Pipe
    | Semicolon
    | Equals
    | Not
    | And
    | Or
    | ForAll
    | Exists
    | FullStop

    -- two-character symbols
    | RightArrow
    | NotEquals
    | DoubleColon
    | DoubleHyphen

    -- literals
    | Identifier

    -- keywords
    | Injective
    | Fn
    | Enum

    | Space -- gets filtered out during tokenising
    | EndOfFile
deriving Repr, BEq

instance : ToString TokenType where
    toString token :=
        match token with
        | TokenType.Space => " "
        | TokenType.LeftParen => ")"
        | TokenType.RightParen => "("
        | TokenType.Pipe => "|"
        | TokenType.Semicolon => ";"
        | TokenType.Equals => "="
        | TokenType.FullStop => "."
        | TokenType.Not => "¬"
        | TokenType.ForAll => "∀"
        | TokenType.Exists => "∃"
        | TokenType.Or => "∨"
        | TokenType.And => "∧"
        | TokenType.RightArrow => "->"
        | TokenType.NotEquals => "!="
        | TokenType.DoubleColon => "::"
        | TokenType.Identifier => "<identifier>"
        | TokenType.Enum => "enum"
        | TokenType.Fn => "fn"
        | TokenType.DoubleHyphen => "--"
        | TokenType.Injective => "injective"
        | TokenType.EndOfFile => "¬"

def scanToken (code : String) : (Nat × Except Char TokenType) :=
    match code.data with
        | ' ' :: _ => (1, Except.ok TokenType.Space)
        | '-' :: '-' :: _ => (1, Except.ok TokenType.DoubleHyphen)
        | '(' :: _ => (1, Except.ok TokenType.LeftParen)
        | ')' :: _ => (1, Except.ok TokenType.RightParen)
        | '|' :: _ => (1, Except.ok TokenType.Pipe)
        | ';' :: _ => (1, Except.ok TokenType.Semicolon)
        | '=' :: _ => (1, Except.ok TokenType.Equals)
        | '.' :: _ => (1, Except.ok TokenType.FullStop)
        | '¬' :: _ => (1, Except.ok TokenType.Not)
        | '∀' :: _ => (1, Except.ok TokenType.ForAll)
        | '∃' :: _ => (1, Except.ok TokenType.Exists)
        | '∨' :: _ => (1, Except.ok TokenType.Or)
        | '∧' :: _ => (1, Except.ok TokenType.And)
        | '-' :: '>' :: _ => (2, Except.ok TokenType.RightArrow)
        | '!' :: '=' :: _ => (2, Except.ok TokenType.NotEquals)
        | ':' :: ':' :: _ => (2, Except.ok TokenType.DoubleColon)
        | x :: _ =>
            if x.isAlpha then
                let identifierTerm := code.takeWhile Char.isAlpha
                let tokenType : TokenType :=
                    if identifierTerm = "fn" then .Fn
                    else if identifierTerm = "injective" then .Injective
                    else if identifierTerm = "enum" then .Enum
                    else .Identifier
                (identifierTerm.length, Except.ok tokenType)
            else
                (1, Except.error x)
        | [] => (0, Except.ok .EndOfFile)

structure Token where -- meaningless defaults make testing/debugging faster and easier as we don't have to write everything out
    tokenType : TokenType
    lexeme : String := "<lexeme>"
    lineNumber : Nat := 0
    colNumber : Nat := 0
deriving Repr

def scanTokens (code : String) (lineNumber : Nat) : Except String (List Token) :=
    if code.trim.startsWith "--" then .ok [] else -- i.e., don't scan comments

    let originalCodeLength := code.length
    let rec aux (code : String) : Except String (List Token) :=
        let colNumber := originalCodeLength - code.length
        match scanToken code with
        | (_, Except.ok TokenType.EndOfFile) => Except.ok []
        | (charsToDrop, Except.ok x) =>
            let tokenStruct := {
                tokenType := x,
                lexeme := code.take charsToDrop,
                lineNumber := lineNumber + 1, -- zero-indexed, but shouldn't be for error messages
                colNumber := colNumber
            }
            let remainingCodeToScan := code.drop charsToDrop
            if (remainingCodeToScan.length < code.length) then
                aux remainingCodeToScan >>= (λc => pure (tokenStruct :: c))
            else
                Except.error s!"an error occurred; scanner got stuck on line {lineNumber}, column {colNumber}"
        | (_, Except.error e) =>
            let msg := s!"unexpected character `{e}` on line {lineNumber}, column {colNumber}"
            Except.error msg

    (λlst => lst.filter (λtoken => token.tokenType != TokenType.Space)) <$> aux code

    termination_by aux code => code.length
