module ParseGlue where

data ParseResult a = OkP a | FailP String
type P a = String -> Int -> ParseResult a

thenP :: P a -> (a -> P b) -> P b
m `thenP`  k = \ s l -> 
  case m s l of 
    OkP a -> k a s l
    FailP s -> FailP s

returnP :: a -> P a
returnP m _ _ = OkP m

failP :: String -> P a
failP s s' _ = FailP (s ++ ":" ++ s')

data Token =
   TKoparen
 | TKcparen
 | TKosquare
 | TKcsquare
 | TKcomma
 | TKdot
 | TKvline
 | TKampersand
 | TKat
 | TKcolon
 | TKlangle
 | TKrangle
 | TKbang
 | TKquestion
 | TKequal
 | TKtilde
 | TKdollar
 | TKroof
 | TKthf
 | TKaxiom
 | TKlemma
 | TKhypothesis
 | TKdefinition
 | TKconjecture
 | TKtype
 | TKinclude
 | TKuppercasename String
 | TKlowercasename String
 | TKstring String
 | TKEOF

{-
   TKoparen
 | TKcparen
 | TKosquare
 | TKcsquare
 | TKocurly
 | TKccurly
 | TKcolon
 | TKsemicolon
 | TKstar
 | TKstarquestion
 | TKrarrow 
 | TKlambda
 | TKquestion
 | TKequal
 | TKdot
 | TKdollar
 | TKhash
 | TKprocent
 | TKdata
 | TKcase
 | TKmutual
 | TKpostulate
 | TKname String
 | TKnumber Int
 | TKEOF
-}
