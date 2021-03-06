module Lex where

import Data.Char

import ParseGlue

isNameChar c = isAlpha c || isDigit c || (c == '_') || (c == '\'') 


lexer :: (Token -> P a) -> P a 
lexer cont [] = cont TKEOF []
lexer cont ('\n':cs) = \line -> lexer cont cs (line+1)
lexer cont ('%':cs) = lexer cont (dropWhile (/= '\n') cs)
lexer cont cs = case ms cs of
 Just (tok, cs) -> cont tok cs
 Nothing -> case ms2 cs of
  Just (tok, cs) -> cont tok cs
  Nothing -> case cs of
   (c:cs) | isSpace c -> lexer cont cs
   (c:cs) | isAlpha c && isLower c || (c == '_') || isDigit c -> lexName cont TKlowercasename (c:cs)
   (c:cs) | isAlpha c && isUpper c || (c == '_') -> lexName cont TKuppercasename (c:cs)
   ('\'':cs) -> let (s, rest) = spanstring cs in cont (TKstring s) rest
   (c:cs) -> failP "invalid character" [c]

ms cs = f l
 where f [] = Nothing
       f ((s, c) : l) = if take (length s) cs == s then Just (c, drop (length s) cs) else f l
       l = [("(", TKoparen),
            (")", TKcparen),
            ("[", TKosquare),
            ("]", TKcsquare),
            (",", TKcomma),
            (".", TKdot),
            ("|", TKvline),
            ("&", TKampersand),
            ("@", TKat),
            (":", TKcolon),
            ("<", TKlangle),
            (">", TKrangle),
            ("!", TKbang),
            ("?", TKquestion),
            ("=", TKequal),
            ("~", TKtilde),
            ("$", TKdollar),
            ("^", TKroof)
           ]

ms2 cs = f l
 where f [] = Nothing
       f ((s, c) : l) = if take (length s) cs == s && not (isNameChar (head (drop (length s) cs))) then Just (c, drop (length s) cs) else f l
       l = [("thf", TKthf),
            ("axiom", TKaxiom),
            ("lemma", TKlemma),
            ("hypothesis", TKhypothesis),
            ("definition", TKdefinition),
            ("conjecture", TKconjecture),
            ("type", TKtype),
            ("include", TKinclude)
           ]


lexName cont cstr cs = cont (cstr name) rest
   where (name,rest) = span isNameChar cs
spanstring [] = ([], [])
spanstring ('\\' : '\'' : xs) = let (ys, zs) = spanstring xs in ('\\' : '\'' : ys, zs)
spanstring ('\'' : xs) = ([], xs)
spanstring (x : xs) = let (ys, zs) = spanstring xs in (x : ys, zs)


