module TPTPSyntax where

data TPTPInput = AnnotatedFormula ThfAnnotated
               | Include String
 deriving Show

data ThfAnnotated = ThfAnnotated String FormulaRole ThfLogicFormula Annotations
 deriving Show

data Annotations = NoAnnotation
 deriving Show

data FormulaRole = Axiom | Lemma | Hypothesis | Definition | Conjecture | Type
 deriving (Show, Eq)

type ThfLogicFormula = Form

data Form = Bin Bin Form Form
          | Un Un Form
          | Quant Quant [VarDecl] Form
          | Typed Form Type
          | Var String
          | Const String
          | DefType String
          | UnTerm Un
 deriving Show

data Bin = Or | And | App | Map | Equal | NotEqual | Equiv | NotEquiv | Implies | LeftImplies
 deriving Show

data Un = Not | UnForall | UnExists | UnAnd | UnOr | UnImplies
 deriving Show

data Quant = Forall | Exists | LambdaAbs
 deriving Show



type VarDecl = (String, Maybe Type)

type Type = Form

