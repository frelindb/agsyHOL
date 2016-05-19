{
{-# OPTIONS -fglasgow-exts #-}

module Parser ( parse ) where

import TPTPSyntax
import ParseGlue
import Lex

}

%name parse
%tokentype { Token }

%token
 '('		{ TKoparen }
 ')'		{ TKcparen }
 '['		{ TKosquare }
 ']'		{ TKcsquare }
 ','  { TKcomma }
 '.'  { TKdot }
 '|'  { TKvline }
 '&'  { TKampersand }
 '@'  { TKat }
 ':'  { TKcolon }
 '<'  { TKlangle }
 '>'  { TKrangle }
 '!'  { TKbang }
 '?'  { TKquestion }
 '='  { TKequal }
 '~'  { TKtilde }
 '$'  { TKdollar }
 '^'  { TKroof }
 'thf'  { TKthf }
 'axiom'  { TKaxiom }
 'lemma'  { TKlemma }
 'hypothesis'  { TKhypothesis }
 'definition'  { TKdefinition }
 'conjecture'  { TKconjecture }
 'type'  { TKtype }
 'include' { TKinclude }

 UPPERCASENAME		{ TKuppercasename $$ }
 LOWERCASENAME		{ TKlowercasename $$ }
 STRING { TKstring $$ }

%monad { P } { thenP } { returnP }
%lexer { lexer } { TKEOF }

%%

TPTP_file :: { [TPTPInput] }
 : { [] }
 | TPTP_input TPTP_file { $1 : $2 }

TPTP_input :: { TPTPInput }
 : annotated_formula { AnnotatedFormula $1 }
 | 'include' '(' string ')' '.' { Include $3 }

annotated_formula :: { ThfAnnotated }
 : thf_annotated { $1 }
-- excluded: <tff_annotated> | <fof_annotated> | <cnf_annotated>

thf_annotated :: { ThfAnnotated }
 : 'thf' '(' name ',' formula_role ',' thf_formula annotations ')' '.' { ThfAnnotated $3 $5 $7 $8 }

annotations :: { Annotations }
 : { NoAnnotation }
-- excluded: ,<source><optional_info>

formula_role :: { FormulaRole }
 : 'axiom' { Axiom }
 | 'lemma' { Lemma }
 | 'hypothesis' { Hypothesis }
 | 'definition' { Definition }
 | 'conjecture' { Conjecture }
 | 'type' { Type }
-- excluded: hypothesis | assumption | theorem | negated_conjecture | plain | fi_domain | fi_functors | fi_predicates | unknown

thf_formula :: { ThfLogicFormula }
 : thf_logic_formula { $1 }
-- excluded: <thf_sequent>

thf_logic_formula :: { Form }
 : thf_binary_formula { $1 }
 | thf_unitary_formula { $1 }
 | thf_type_formula { $1 }
-- excluded: <thf_subtype>

thf_binary_formula :: { Form }
 : thf_binary_pair { $1 }
 | thf_binary_tuple { $1 }
 | thf_binary_type { $1 }

thf_binary_pair :: { Form }
 : thf_unitary_formula thf_pair_connective thf_unitary_formula { Bin $2 $1 $3 }

thf_binary_tuple :: { Form }
 : thf_or_formula { $1 }
 | thf_and_formula { $1 }
 | thf_apply_formula { $1 }

thf_or_formula :: { Form }
 : thf_unitary_formula '|' thf_unitary_formula { Bin Or $1 $3 }
 | thf_or_formula '|' thf_unitary_formula { Bin Or $1 $3 }

thf_and_formula :: { Form }
 : thf_unitary_formula '&' thf_unitary_formula { Bin And $1 $3 }
 | thf_and_formula '&' thf_unitary_formula { Bin And $1 $3 }

thf_apply_formula :: { Form }
 : thf_unitary_formula '@' thf_unitary_formula { Bin App $1 $3 }
 | thf_apply_formula '@' thf_unitary_formula { Bin App $1 $3 }

thf_unitary_formula :: { Form }
 : thf_quantified_formula { $1 }
 | thf_unary_formula { $1 }
 | thf_atom { $1 }
 | '(' thf_logic_formula ')' { $2 }
-- excluded: <thf_tuple> | <thf_letrec> | <thf_conditional>

thf_quantified_formula :: { Form }
 : thf_quantifier '[' thf_variable_list ']' ':' thf_unitary_formula { Quant $1 $3 $6 }

thf_variable_list :: { [VarDecl] }
 : thf_variable { $1 : [] }
 | thf_variable ',' thf_variable_list { $1 : $3 }

thf_variable :: { VarDecl }
 : thf_typed_variable { $1 }
 | variable { ($1, Nothing) }

thf_typed_variable :: { VarDecl }
 : variable ':' thf_top_level_type { ($1, Just $3) }

thf_unary_formula :: { Form }
 : thf_unary_connective '(' thf_logic_formula ')' { Un $1 $3 }

thf_type_formula :: { Form }
 : thf_typeable_formula ':' thf_top_level_type { Typed $1 $3 }

thf_typeable_formula :: { Form }
 : thf_atom { $1 }
 | '(' thf_logic_formula ')' { $2 }
-- excluded: <thf_tuple>

thf_top_level_type :: { Form }
 : thf_logic_formula { $1 }

thf_unitary_type :: { Form }
 : thf_unitary_formula { $1 }

thf_binary_type :: { Form }
 : thf_mapping_type { $1 }
-- excluded: <thf_xprod_type> | <thf_union_type>

thf_mapping_type :: { Form }
 : thf_unitary_type '>' thf_unitary_type { Bin Map $1 $3 }
 | thf_unitary_type '>' thf_mapping_type { Bin Map $1 $3 }

thf_quantifier :: { Quant }
 : fol_quantifier { $1 }
 | '^' { LambdaAbs }
-- excluded: !> | ?* | @+ | @-

fol_quantifier :: { Quant }
 : '!' { Forall }
 | '?' { Exists }

thf_pair_connective :: { Bin }
 : '=' { Equal }
 | '!' '=' { NotEqual }
 | binary_connective { $1 }

thf_unary_connective :: { Un }
 : unary_connective { $1 }
 | '?' '?' { UnExists }
 | '!' '!' { UnForall }
 | '&' { UnAnd }
 | '|' { UnOr }
 | '=' '>'  { UnImplies }
-- excluded: !! | ??

binary_connective :: { Bin }
 : '<' '=' '>' { Equiv }
 | '<' '~' '>' { NotEquiv }
 | '=' '>' { Implies }
 | '<' '=' { LeftImplies }
-- excluded: ~<vline> | ~&

unary_connective :: { Un }
 : '~' { Not }

thf_atom :: { Form }
 : term { $1 }
 | defined_type { $1 }
 | thf_conn_term { $1 }
-- included: <defined_type>

thf_conn_term :: { Form }
 : thf_unary_connective { UnTerm $1 }
-- exluded: <thf_pair_connective> | <assoc_connective>

term :: { Form }
 : function_term { $1 }
 | variable { Var $1 }
-- excluded: <conditional_term>

function_term :: { Form }
 : plain_term { $1 }
-- excluded: <defined_term> | <system_term>

plain_term :: { Form }
 : constant { $1 }
-- excluded: <functor>(<arguments>)

constant :: { Form }
 : functor { Const $1 }

defined_type :: { Form }
 : atomic_defined_word { DefType $1 }

atomic_defined_word :: { String }
 : '$' LOWERCASENAME { $2 }

name :: { String }
 : LOWERCASENAME { $1 }
 | STRING { "\'" ++ $1 ++ "\'" }
 | 'conjecture' { "conjecture" }

functor :: { String }
 : LOWERCASENAME { $1 }
 | STRING { "\'" ++ $1 ++ "\'" }

variable :: { String }
 : UPPERCASENAME { $1 }

string :: { String }
 : STRING { $1 }

{

happyError :: P a 
happyError s l = failP (show l ++ ": Parse error\n") (take 100 s) l

}
