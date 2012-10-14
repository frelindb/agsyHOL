{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts #-}

module Parser ( parse ) where

import TPTPSyntax
import ParseGlue
import Lex

-- parser produced by Happy Version 1.18.6

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 ([TPTPInput])
	| HappyAbsSyn5 (TPTPInput)
	| HappyAbsSyn6 (ThfAnnotated)
	| HappyAbsSyn8 (Annotations)
	| HappyAbsSyn9 (FormulaRole)
	| HappyAbsSyn10 (ThfLogicFormula)
	| HappyAbsSyn11 (Form)
	| HappyAbsSyn20 ([VarDecl])
	| HappyAbsSyn21 (VarDecl)
	| HappyAbsSyn30 (Quant)
	| HappyAbsSyn32 (Bin)
	| HappyAbsSyn33 (Un)
	| HappyAbsSyn43 (String)

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64,
 action_65,
 action_66,
 action_67,
 action_68,
 action_69,
 action_70,
 action_71,
 action_72,
 action_73,
 action_74,
 action_75,
 action_76,
 action_77,
 action_78,
 action_79,
 action_80,
 action_81,
 action_82,
 action_83,
 action_84,
 action_85,
 action_86,
 action_87,
 action_88,
 action_89,
 action_90,
 action_91,
 action_92,
 action_93,
 action_94,
 action_95,
 action_96,
 action_97,
 action_98,
 action_99,
 action_100,
 action_101,
 action_102,
 action_103,
 action_104,
 action_105,
 action_106,
 action_107,
 action_108,
 action_109,
 action_110,
 action_111,
 action_112,
 action_113,
 action_114,
 action_115,
 action_116,
 action_117,
 action_118,
 action_119,
 action_120,
 action_121,
 action_122,
 action_123,
 action_124,
 action_125,
 action_126,
 action_127,
 action_128 :: () => Int -> ({-HappyReduction (P) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> (P) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> (P) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> (P) HappyAbsSyn)

happyReduce_1,
 happyReduce_2,
 happyReduce_3,
 happyReduce_4,
 happyReduce_5,
 happyReduce_6,
 happyReduce_7,
 happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38,
 happyReduce_39,
 happyReduce_40,
 happyReduce_41,
 happyReduce_42,
 happyReduce_43,
 happyReduce_44,
 happyReduce_45,
 happyReduce_46,
 happyReduce_47,
 happyReduce_48,
 happyReduce_49,
 happyReduce_50,
 happyReduce_51,
 happyReduce_52,
 happyReduce_53,
 happyReduce_54,
 happyReduce_55,
 happyReduce_56,
 happyReduce_57,
 happyReduce_58,
 happyReduce_59,
 happyReduce_60,
 happyReduce_61,
 happyReduce_62,
 happyReduce_63,
 happyReduce_64,
 happyReduce_65,
 happyReduce_66,
 happyReduce_67,
 happyReduce_68,
 happyReduce_69,
 happyReduce_70,
 happyReduce_71,
 happyReduce_72,
 happyReduce_73,
 happyReduce_74,
 happyReduce_75,
 happyReduce_76,
 happyReduce_77,
 happyReduce_78,
 happyReduce_79,
 happyReduce_80,
 happyReduce_81,
 happyReduce_82,
 happyReduce_83,
 happyReduce_84,
 happyReduce_85 :: () => ({-HappyReduction (P) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> (P) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> (P) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> (P) HappyAbsSyn)

action_0 (66) = happyShift action_6
action_0 (73) = happyShift action_7
action_0 (4) = happyGoto action_2
action_0 (5) = happyGoto action_3
action_0 (6) = happyGoto action_4
action_0 (7) = happyGoto action_5
action_0 _ = happyReduce_1

action_1 _ = happyFail

action_2 (77) = happyAccept
action_2 _ = happyFail

action_3 (66) = happyShift action_6
action_3 (73) = happyShift action_7
action_3 (4) = happyGoto action_10
action_3 (5) = happyGoto action_3
action_3 (6) = happyGoto action_4
action_3 (7) = happyGoto action_5
action_3 _ = happyReduce_1

action_4 _ = happyReduce_3

action_5 _ = happyReduce_5

action_6 (48) = happyShift action_9
action_6 _ = happyFail

action_7 (48) = happyShift action_8
action_7 _ = happyFail

action_8 (76) = happyShift action_16
action_8 (47) = happyGoto action_15
action_8 _ = happyFail

action_9 (71) = happyShift action_12
action_9 (75) = happyShift action_13
action_9 (76) = happyShift action_14
action_9 (44) = happyGoto action_11
action_9 _ = happyFail

action_10 _ = happyReduce_2

action_11 (52) = happyShift action_18
action_11 _ = happyFail

action_12 _ = happyReduce_81

action_13 _ = happyReduce_79

action_14 _ = happyReduce_80

action_15 (49) = happyShift action_17
action_15 _ = happyFail

action_16 _ = happyReduce_85

action_17 (53) = happyShift action_26
action_17 _ = happyFail

action_18 (67) = happyShift action_20
action_18 (68) = happyShift action_21
action_18 (69) = happyShift action_22
action_18 (70) = happyShift action_23
action_18 (71) = happyShift action_24
action_18 (72) = happyShift action_25
action_18 (9) = happyGoto action_19
action_18 _ = happyFail

action_19 (52) = happyShift action_27
action_19 _ = happyFail

action_20 _ = happyReduce_8

action_21 _ = happyReduce_9

action_22 _ = happyReduce_10

action_23 _ = happyReduce_11

action_24 _ = happyReduce_12

action_25 _ = happyReduce_13

action_26 _ = happyReduce_4

action_27 (48) = happyShift action_58
action_27 (54) = happyShift action_59
action_27 (55) = happyShift action_60
action_27 (60) = happyShift action_61
action_27 (61) = happyShift action_62
action_27 (62) = happyShift action_63
action_27 (63) = happyShift action_64
action_27 (64) = happyShift action_65
action_27 (65) = happyShift action_66
action_27 (74) = happyShift action_67
action_27 (75) = happyShift action_68
action_27 (76) = happyShift action_69
action_27 (10) = happyGoto action_28
action_27 (11) = happyGoto action_29
action_27 (12) = happyGoto action_30
action_27 (13) = happyGoto action_31
action_27 (14) = happyGoto action_32
action_27 (15) = happyGoto action_33
action_27 (16) = happyGoto action_34
action_27 (17) = happyGoto action_35
action_27 (18) = happyGoto action_36
action_27 (19) = happyGoto action_37
action_27 (23) = happyGoto action_38
action_27 (24) = happyGoto action_39
action_27 (25) = happyGoto action_40
action_27 (27) = happyGoto action_41
action_27 (28) = happyGoto action_42
action_27 (29) = happyGoto action_43
action_27 (30) = happyGoto action_44
action_27 (31) = happyGoto action_45
action_27 (33) = happyGoto action_46
action_27 (35) = happyGoto action_47
action_27 (36) = happyGoto action_48
action_27 (37) = happyGoto action_49
action_27 (38) = happyGoto action_50
action_27 (39) = happyGoto action_51
action_27 (40) = happyGoto action_52
action_27 (41) = happyGoto action_53
action_27 (42) = happyGoto action_54
action_27 (43) = happyGoto action_55
action_27 (45) = happyGoto action_56
action_27 (46) = happyGoto action_57
action_27 _ = happyFail

action_28 (8) = happyGoto action_90
action_28 _ = happyReduce_7

action_29 _ = happyReduce_14

action_30 _ = happyReduce_15

action_31 _ = happyReduce_18

action_32 _ = happyReduce_19

action_33 (54) = happyShift action_89
action_33 _ = happyReduce_22

action_34 (55) = happyShift action_88
action_34 _ = happyReduce_23

action_35 (56) = happyShift action_87
action_35 _ = happyReduce_24

action_36 (54) = happyShift action_81
action_36 (55) = happyShift action_82
action_36 (56) = happyShift action_83
action_36 (58) = happyShift action_84
action_36 (59) = happyReduce_46
action_36 (60) = happyShift action_85
action_36 (62) = happyShift action_86
action_36 (32) = happyGoto action_79
action_36 (34) = happyGoto action_80
action_36 _ = happyReduce_16

action_37 _ = happyReduce_31

action_38 _ = happyReduce_32

action_39 _ = happyReduce_17

action_40 (57) = happyShift action_78
action_40 _ = happyFail

action_41 (59) = happyShift action_77
action_41 _ = happyFail

action_42 _ = happyReduce_20

action_43 _ = happyReduce_47

action_44 (50) = happyShift action_76
action_44 _ = happyFail

action_45 _ = happyReduce_50

action_46 (48) = happyShift action_75
action_46 _ = happyReduce_71

action_47 _ = happyReduce_57

action_48 (57) = happyReduce_43
action_48 _ = happyReduce_33

action_49 _ = happyReduce_70

action_50 _ = happyReduce_68

action_51 _ = happyReduce_72

action_52 _ = happyReduce_74

action_53 _ = happyReduce_75

action_54 _ = happyReduce_69

action_55 _ = happyReduce_77

action_56 _ = happyReduce_76

action_57 _ = happyReduce_73

action_58 (48) = happyShift action_58
action_58 (54) = happyShift action_59
action_58 (55) = happyShift action_60
action_58 (60) = happyShift action_61
action_58 (61) = happyShift action_62
action_58 (62) = happyShift action_63
action_58 (63) = happyShift action_64
action_58 (64) = happyShift action_65
action_58 (65) = happyShift action_66
action_58 (74) = happyShift action_67
action_58 (75) = happyShift action_68
action_58 (76) = happyShift action_69
action_58 (11) = happyGoto action_74
action_58 (12) = happyGoto action_30
action_58 (13) = happyGoto action_31
action_58 (14) = happyGoto action_32
action_58 (15) = happyGoto action_33
action_58 (16) = happyGoto action_34
action_58 (17) = happyGoto action_35
action_58 (18) = happyGoto action_36
action_58 (19) = happyGoto action_37
action_58 (23) = happyGoto action_38
action_58 (24) = happyGoto action_39
action_58 (25) = happyGoto action_40
action_58 (27) = happyGoto action_41
action_58 (28) = happyGoto action_42
action_58 (29) = happyGoto action_43
action_58 (30) = happyGoto action_44
action_58 (31) = happyGoto action_45
action_58 (33) = happyGoto action_46
action_58 (35) = happyGoto action_47
action_58 (36) = happyGoto action_48
action_58 (37) = happyGoto action_49
action_58 (38) = happyGoto action_50
action_58 (39) = happyGoto action_51
action_58 (40) = happyGoto action_52
action_58 (41) = happyGoto action_53
action_58 (42) = happyGoto action_54
action_58 (43) = happyGoto action_55
action_58 (45) = happyGoto action_56
action_58 (46) = happyGoto action_57
action_58 _ = happyFail

action_59 _ = happyReduce_61

action_60 _ = happyReduce_60

action_61 (60) = happyShift action_73
action_61 _ = happyReduce_52

action_62 (61) = happyShift action_72
action_62 _ = happyReduce_53

action_63 (59) = happyShift action_71
action_63 _ = happyFail

action_64 _ = happyReduce_67

action_65 (75) = happyShift action_70
action_65 _ = happyFail

action_66 _ = happyReduce_51

action_67 _ = happyReduce_84

action_68 _ = happyReduce_82

action_69 _ = happyReduce_83

action_70 _ = happyReduce_78

action_71 _ = happyReduce_62

action_72 _ = happyReduce_58

action_73 _ = happyReduce_59

action_74 (49) = happyShift action_115
action_74 _ = happyFail

action_75 (48) = happyShift action_58
action_75 (54) = happyShift action_59
action_75 (55) = happyShift action_60
action_75 (60) = happyShift action_61
action_75 (61) = happyShift action_62
action_75 (62) = happyShift action_63
action_75 (63) = happyShift action_64
action_75 (64) = happyShift action_65
action_75 (65) = happyShift action_66
action_75 (74) = happyShift action_67
action_75 (75) = happyShift action_68
action_75 (76) = happyShift action_69
action_75 (11) = happyGoto action_114
action_75 (12) = happyGoto action_30
action_75 (13) = happyGoto action_31
action_75 (14) = happyGoto action_32
action_75 (15) = happyGoto action_33
action_75 (16) = happyGoto action_34
action_75 (17) = happyGoto action_35
action_75 (18) = happyGoto action_36
action_75 (19) = happyGoto action_37
action_75 (23) = happyGoto action_38
action_75 (24) = happyGoto action_39
action_75 (25) = happyGoto action_40
action_75 (27) = happyGoto action_41
action_75 (28) = happyGoto action_42
action_75 (29) = happyGoto action_43
action_75 (30) = happyGoto action_44
action_75 (31) = happyGoto action_45
action_75 (33) = happyGoto action_46
action_75 (35) = happyGoto action_47
action_75 (36) = happyGoto action_48
action_75 (37) = happyGoto action_49
action_75 (38) = happyGoto action_50
action_75 (39) = happyGoto action_51
action_75 (40) = happyGoto action_52
action_75 (41) = happyGoto action_53
action_75 (42) = happyGoto action_54
action_75 (43) = happyGoto action_55
action_75 (45) = happyGoto action_56
action_75 (46) = happyGoto action_57
action_75 _ = happyFail

action_76 (74) = happyShift action_67
action_76 (20) = happyGoto action_110
action_76 (21) = happyGoto action_111
action_76 (22) = happyGoto action_112
action_76 (46) = happyGoto action_113
action_76 _ = happyFail

action_77 (48) = happyShift action_94
action_77 (54) = happyShift action_59
action_77 (55) = happyShift action_60
action_77 (60) = happyShift action_61
action_77 (61) = happyShift action_62
action_77 (62) = happyShift action_63
action_77 (63) = happyShift action_64
action_77 (64) = happyShift action_65
action_77 (65) = happyShift action_66
action_77 (74) = happyShift action_67
action_77 (75) = happyShift action_68
action_77 (76) = happyShift action_69
action_77 (18) = happyGoto action_107
action_77 (19) = happyGoto action_37
action_77 (23) = happyGoto action_38
action_77 (27) = happyGoto action_108
action_77 (29) = happyGoto action_109
action_77 (30) = happyGoto action_44
action_77 (31) = happyGoto action_45
action_77 (33) = happyGoto action_46
action_77 (35) = happyGoto action_47
action_77 (36) = happyGoto action_93
action_77 (37) = happyGoto action_49
action_77 (38) = happyGoto action_50
action_77 (39) = happyGoto action_51
action_77 (40) = happyGoto action_52
action_77 (41) = happyGoto action_53
action_77 (42) = happyGoto action_54
action_77 (43) = happyGoto action_55
action_77 (45) = happyGoto action_56
action_77 (46) = happyGoto action_57
action_77 _ = happyFail

action_78 (48) = happyShift action_58
action_78 (54) = happyShift action_59
action_78 (55) = happyShift action_60
action_78 (60) = happyShift action_61
action_78 (61) = happyShift action_62
action_78 (62) = happyShift action_63
action_78 (63) = happyShift action_64
action_78 (64) = happyShift action_65
action_78 (65) = happyShift action_66
action_78 (74) = happyShift action_67
action_78 (75) = happyShift action_68
action_78 (76) = happyShift action_69
action_78 (11) = happyGoto action_105
action_78 (12) = happyGoto action_30
action_78 (13) = happyGoto action_31
action_78 (14) = happyGoto action_32
action_78 (15) = happyGoto action_33
action_78 (16) = happyGoto action_34
action_78 (17) = happyGoto action_35
action_78 (18) = happyGoto action_36
action_78 (19) = happyGoto action_37
action_78 (23) = happyGoto action_38
action_78 (24) = happyGoto action_39
action_78 (25) = happyGoto action_40
action_78 (26) = happyGoto action_106
action_78 (27) = happyGoto action_41
action_78 (28) = happyGoto action_42
action_78 (29) = happyGoto action_43
action_78 (30) = happyGoto action_44
action_78 (31) = happyGoto action_45
action_78 (33) = happyGoto action_46
action_78 (35) = happyGoto action_47
action_78 (36) = happyGoto action_48
action_78 (37) = happyGoto action_49
action_78 (38) = happyGoto action_50
action_78 (39) = happyGoto action_51
action_78 (40) = happyGoto action_52
action_78 (41) = happyGoto action_53
action_78 (42) = happyGoto action_54
action_78 (43) = happyGoto action_55
action_78 (45) = happyGoto action_56
action_78 (46) = happyGoto action_57
action_78 _ = happyFail

action_79 (48) = happyShift action_94
action_79 (54) = happyShift action_59
action_79 (55) = happyShift action_60
action_79 (60) = happyShift action_61
action_79 (61) = happyShift action_62
action_79 (62) = happyShift action_63
action_79 (63) = happyShift action_64
action_79 (64) = happyShift action_65
action_79 (65) = happyShift action_66
action_79 (74) = happyShift action_67
action_79 (75) = happyShift action_68
action_79 (76) = happyShift action_69
action_79 (18) = happyGoto action_104
action_79 (19) = happyGoto action_37
action_79 (23) = happyGoto action_38
action_79 (30) = happyGoto action_44
action_79 (31) = happyGoto action_45
action_79 (33) = happyGoto action_46
action_79 (35) = happyGoto action_47
action_79 (36) = happyGoto action_93
action_79 (37) = happyGoto action_49
action_79 (38) = happyGoto action_50
action_79 (39) = happyGoto action_51
action_79 (40) = happyGoto action_52
action_79 (41) = happyGoto action_53
action_79 (42) = happyGoto action_54
action_79 (43) = happyGoto action_55
action_79 (45) = happyGoto action_56
action_79 (46) = happyGoto action_57
action_79 _ = happyFail

action_80 _ = happyReduce_56

action_81 (48) = happyShift action_94
action_81 (54) = happyShift action_59
action_81 (55) = happyShift action_60
action_81 (60) = happyShift action_61
action_81 (61) = happyShift action_62
action_81 (62) = happyShift action_63
action_81 (63) = happyShift action_64
action_81 (64) = happyShift action_65
action_81 (65) = happyShift action_66
action_81 (74) = happyShift action_67
action_81 (75) = happyShift action_68
action_81 (76) = happyShift action_69
action_81 (18) = happyGoto action_103
action_81 (19) = happyGoto action_37
action_81 (23) = happyGoto action_38
action_81 (30) = happyGoto action_44
action_81 (31) = happyGoto action_45
action_81 (33) = happyGoto action_46
action_81 (35) = happyGoto action_47
action_81 (36) = happyGoto action_93
action_81 (37) = happyGoto action_49
action_81 (38) = happyGoto action_50
action_81 (39) = happyGoto action_51
action_81 (40) = happyGoto action_52
action_81 (41) = happyGoto action_53
action_81 (42) = happyGoto action_54
action_81 (43) = happyGoto action_55
action_81 (45) = happyGoto action_56
action_81 (46) = happyGoto action_57
action_81 _ = happyFail

action_82 (48) = happyShift action_94
action_82 (54) = happyShift action_59
action_82 (55) = happyShift action_60
action_82 (60) = happyShift action_61
action_82 (61) = happyShift action_62
action_82 (62) = happyShift action_63
action_82 (63) = happyShift action_64
action_82 (64) = happyShift action_65
action_82 (65) = happyShift action_66
action_82 (74) = happyShift action_67
action_82 (75) = happyShift action_68
action_82 (76) = happyShift action_69
action_82 (18) = happyGoto action_102
action_82 (19) = happyGoto action_37
action_82 (23) = happyGoto action_38
action_82 (30) = happyGoto action_44
action_82 (31) = happyGoto action_45
action_82 (33) = happyGoto action_46
action_82 (35) = happyGoto action_47
action_82 (36) = happyGoto action_93
action_82 (37) = happyGoto action_49
action_82 (38) = happyGoto action_50
action_82 (39) = happyGoto action_51
action_82 (40) = happyGoto action_52
action_82 (41) = happyGoto action_53
action_82 (42) = happyGoto action_54
action_82 (43) = happyGoto action_55
action_82 (45) = happyGoto action_56
action_82 (46) = happyGoto action_57
action_82 _ = happyFail

action_83 (48) = happyShift action_94
action_83 (54) = happyShift action_59
action_83 (55) = happyShift action_60
action_83 (60) = happyShift action_61
action_83 (61) = happyShift action_62
action_83 (62) = happyShift action_63
action_83 (63) = happyShift action_64
action_83 (64) = happyShift action_65
action_83 (65) = happyShift action_66
action_83 (74) = happyShift action_67
action_83 (75) = happyShift action_68
action_83 (76) = happyShift action_69
action_83 (18) = happyGoto action_101
action_83 (19) = happyGoto action_37
action_83 (23) = happyGoto action_38
action_83 (30) = happyGoto action_44
action_83 (31) = happyGoto action_45
action_83 (33) = happyGoto action_46
action_83 (35) = happyGoto action_47
action_83 (36) = happyGoto action_93
action_83 (37) = happyGoto action_49
action_83 (38) = happyGoto action_50
action_83 (39) = happyGoto action_51
action_83 (40) = happyGoto action_52
action_83 (41) = happyGoto action_53
action_83 (42) = happyGoto action_54
action_83 (43) = happyGoto action_55
action_83 (45) = happyGoto action_56
action_83 (46) = happyGoto action_57
action_83 _ = happyFail

action_84 (62) = happyShift action_99
action_84 (63) = happyShift action_100
action_84 _ = happyFail

action_85 (62) = happyShift action_98
action_85 _ = happyFail

action_86 (59) = happyShift action_97
action_86 _ = happyReduce_54

action_87 (48) = happyShift action_94
action_87 (54) = happyShift action_59
action_87 (55) = happyShift action_60
action_87 (60) = happyShift action_61
action_87 (61) = happyShift action_62
action_87 (62) = happyShift action_63
action_87 (63) = happyShift action_64
action_87 (64) = happyShift action_65
action_87 (65) = happyShift action_66
action_87 (74) = happyShift action_67
action_87 (75) = happyShift action_68
action_87 (76) = happyShift action_69
action_87 (18) = happyGoto action_96
action_87 (19) = happyGoto action_37
action_87 (23) = happyGoto action_38
action_87 (30) = happyGoto action_44
action_87 (31) = happyGoto action_45
action_87 (33) = happyGoto action_46
action_87 (35) = happyGoto action_47
action_87 (36) = happyGoto action_93
action_87 (37) = happyGoto action_49
action_87 (38) = happyGoto action_50
action_87 (39) = happyGoto action_51
action_87 (40) = happyGoto action_52
action_87 (41) = happyGoto action_53
action_87 (42) = happyGoto action_54
action_87 (43) = happyGoto action_55
action_87 (45) = happyGoto action_56
action_87 (46) = happyGoto action_57
action_87 _ = happyFail

action_88 (48) = happyShift action_94
action_88 (54) = happyShift action_59
action_88 (55) = happyShift action_60
action_88 (60) = happyShift action_61
action_88 (61) = happyShift action_62
action_88 (62) = happyShift action_63
action_88 (63) = happyShift action_64
action_88 (64) = happyShift action_65
action_88 (65) = happyShift action_66
action_88 (74) = happyShift action_67
action_88 (75) = happyShift action_68
action_88 (76) = happyShift action_69
action_88 (18) = happyGoto action_95
action_88 (19) = happyGoto action_37
action_88 (23) = happyGoto action_38
action_88 (30) = happyGoto action_44
action_88 (31) = happyGoto action_45
action_88 (33) = happyGoto action_46
action_88 (35) = happyGoto action_47
action_88 (36) = happyGoto action_93
action_88 (37) = happyGoto action_49
action_88 (38) = happyGoto action_50
action_88 (39) = happyGoto action_51
action_88 (40) = happyGoto action_52
action_88 (41) = happyGoto action_53
action_88 (42) = happyGoto action_54
action_88 (43) = happyGoto action_55
action_88 (45) = happyGoto action_56
action_88 (46) = happyGoto action_57
action_88 _ = happyFail

action_89 (48) = happyShift action_94
action_89 (54) = happyShift action_59
action_89 (55) = happyShift action_60
action_89 (60) = happyShift action_61
action_89 (61) = happyShift action_62
action_89 (62) = happyShift action_63
action_89 (63) = happyShift action_64
action_89 (64) = happyShift action_65
action_89 (65) = happyShift action_66
action_89 (74) = happyShift action_67
action_89 (75) = happyShift action_68
action_89 (76) = happyShift action_69
action_89 (18) = happyGoto action_92
action_89 (19) = happyGoto action_37
action_89 (23) = happyGoto action_38
action_89 (30) = happyGoto action_44
action_89 (31) = happyGoto action_45
action_89 (33) = happyGoto action_46
action_89 (35) = happyGoto action_47
action_89 (36) = happyGoto action_93
action_89 (37) = happyGoto action_49
action_89 (38) = happyGoto action_50
action_89 (39) = happyGoto action_51
action_89 (40) = happyGoto action_52
action_89 (41) = happyGoto action_53
action_89 (42) = happyGoto action_54
action_89 (43) = happyGoto action_55
action_89 (45) = happyGoto action_56
action_89 (46) = happyGoto action_57
action_89 _ = happyFail

action_90 (49) = happyShift action_91
action_90 _ = happyFail

action_91 (53) = happyShift action_123
action_91 _ = happyFail

action_92 _ = happyReduce_26

action_93 _ = happyReduce_33

action_94 (48) = happyShift action_58
action_94 (54) = happyShift action_59
action_94 (55) = happyShift action_60
action_94 (60) = happyShift action_61
action_94 (61) = happyShift action_62
action_94 (62) = happyShift action_63
action_94 (63) = happyShift action_64
action_94 (64) = happyShift action_65
action_94 (65) = happyShift action_66
action_94 (74) = happyShift action_67
action_94 (75) = happyShift action_68
action_94 (76) = happyShift action_69
action_94 (11) = happyGoto action_122
action_94 (12) = happyGoto action_30
action_94 (13) = happyGoto action_31
action_94 (14) = happyGoto action_32
action_94 (15) = happyGoto action_33
action_94 (16) = happyGoto action_34
action_94 (17) = happyGoto action_35
action_94 (18) = happyGoto action_36
action_94 (19) = happyGoto action_37
action_94 (23) = happyGoto action_38
action_94 (24) = happyGoto action_39
action_94 (25) = happyGoto action_40
action_94 (27) = happyGoto action_41
action_94 (28) = happyGoto action_42
action_94 (29) = happyGoto action_43
action_94 (30) = happyGoto action_44
action_94 (31) = happyGoto action_45
action_94 (33) = happyGoto action_46
action_94 (35) = happyGoto action_47
action_94 (36) = happyGoto action_48
action_94 (37) = happyGoto action_49
action_94 (38) = happyGoto action_50
action_94 (39) = happyGoto action_51
action_94 (40) = happyGoto action_52
action_94 (41) = happyGoto action_53
action_94 (42) = happyGoto action_54
action_94 (43) = happyGoto action_55
action_94 (45) = happyGoto action_56
action_94 (46) = happyGoto action_57
action_94 _ = happyFail

action_95 _ = happyReduce_28

action_96 _ = happyReduce_30

action_97 _ = happyReduce_65

action_98 _ = happyReduce_55

action_99 (59) = happyShift action_121
action_99 _ = happyReduce_66

action_100 (59) = happyShift action_120
action_100 _ = happyFail

action_101 _ = happyReduce_29

action_102 _ = happyReduce_27

action_103 _ = happyReduce_25

action_104 _ = happyReduce_21

action_105 _ = happyReduce_45

action_106 _ = happyReduce_42

action_107 _ = happyReduce_46

action_108 (59) = happyShift action_77
action_108 _ = happyReduce_48

action_109 _ = happyReduce_49

action_110 (51) = happyShift action_119
action_110 _ = happyFail

action_111 (52) = happyShift action_118
action_111 _ = happyReduce_36

action_112 _ = happyReduce_38

action_113 (57) = happyShift action_117
action_113 _ = happyReduce_39

action_114 (49) = happyShift action_116
action_114 _ = happyFail

action_115 (57) = happyReduce_44
action_115 _ = happyReduce_34

action_116 _ = happyReduce_41

action_117 (48) = happyShift action_58
action_117 (54) = happyShift action_59
action_117 (55) = happyShift action_60
action_117 (60) = happyShift action_61
action_117 (61) = happyShift action_62
action_117 (62) = happyShift action_63
action_117 (63) = happyShift action_64
action_117 (64) = happyShift action_65
action_117 (65) = happyShift action_66
action_117 (74) = happyShift action_67
action_117 (75) = happyShift action_68
action_117 (76) = happyShift action_69
action_117 (11) = happyGoto action_105
action_117 (12) = happyGoto action_30
action_117 (13) = happyGoto action_31
action_117 (14) = happyGoto action_32
action_117 (15) = happyGoto action_33
action_117 (16) = happyGoto action_34
action_117 (17) = happyGoto action_35
action_117 (18) = happyGoto action_36
action_117 (19) = happyGoto action_37
action_117 (23) = happyGoto action_38
action_117 (24) = happyGoto action_39
action_117 (25) = happyGoto action_40
action_117 (26) = happyGoto action_127
action_117 (27) = happyGoto action_41
action_117 (28) = happyGoto action_42
action_117 (29) = happyGoto action_43
action_117 (30) = happyGoto action_44
action_117 (31) = happyGoto action_45
action_117 (33) = happyGoto action_46
action_117 (35) = happyGoto action_47
action_117 (36) = happyGoto action_48
action_117 (37) = happyGoto action_49
action_117 (38) = happyGoto action_50
action_117 (39) = happyGoto action_51
action_117 (40) = happyGoto action_52
action_117 (41) = happyGoto action_53
action_117 (42) = happyGoto action_54
action_117 (43) = happyGoto action_55
action_117 (45) = happyGoto action_56
action_117 (46) = happyGoto action_57
action_117 _ = happyFail

action_118 (74) = happyShift action_67
action_118 (20) = happyGoto action_126
action_118 (21) = happyGoto action_111
action_118 (22) = happyGoto action_112
action_118 (46) = happyGoto action_113
action_118 _ = happyFail

action_119 (57) = happyShift action_125
action_119 _ = happyFail

action_120 _ = happyReduce_64

action_121 _ = happyReduce_63

action_122 (49) = happyShift action_124
action_122 _ = happyFail

action_123 _ = happyReduce_6

action_124 _ = happyReduce_34

action_125 (48) = happyShift action_94
action_125 (54) = happyShift action_59
action_125 (55) = happyShift action_60
action_125 (60) = happyShift action_61
action_125 (61) = happyShift action_62
action_125 (62) = happyShift action_63
action_125 (63) = happyShift action_64
action_125 (64) = happyShift action_65
action_125 (65) = happyShift action_66
action_125 (74) = happyShift action_67
action_125 (75) = happyShift action_68
action_125 (76) = happyShift action_69
action_125 (18) = happyGoto action_128
action_125 (19) = happyGoto action_37
action_125 (23) = happyGoto action_38
action_125 (30) = happyGoto action_44
action_125 (31) = happyGoto action_45
action_125 (33) = happyGoto action_46
action_125 (35) = happyGoto action_47
action_125 (36) = happyGoto action_93
action_125 (37) = happyGoto action_49
action_125 (38) = happyGoto action_50
action_125 (39) = happyGoto action_51
action_125 (40) = happyGoto action_52
action_125 (41) = happyGoto action_53
action_125 (42) = happyGoto action_54
action_125 (43) = happyGoto action_55
action_125 (45) = happyGoto action_56
action_125 (46) = happyGoto action_57
action_125 _ = happyFail

action_126 _ = happyReduce_37

action_127 _ = happyReduce_40

action_128 _ = happyReduce_35

happyReduce_1 = happySpecReduce_0  4 happyReduction_1
happyReduction_1  =  HappyAbsSyn4
		 ([]
	)

happyReduce_2 = happySpecReduce_2  4 happyReduction_2
happyReduction_2 (HappyAbsSyn4  happy_var_2)
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_1 : happy_var_2
	)
happyReduction_2 _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_1  5 happyReduction_3
happyReduction_3 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn5
		 (AnnotatedFormula happy_var_1
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happyReduce 5 5 happyReduction_4
happyReduction_4 (_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Include happy_var_3
	) `HappyStk` happyRest

happyReduce_5 = happySpecReduce_1  6 happyReduction_5
happyReduction_5 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (happy_var_1
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happyReduce 10 7 happyReduction_6
happyReduction_6 (_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_8) `HappyStk`
	(HappyAbsSyn10  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (ThfAnnotated happy_var_3 happy_var_5 happy_var_7 happy_var_8
	) `HappyStk` happyRest

happyReduce_7 = happySpecReduce_0  8 happyReduction_7
happyReduction_7  =  HappyAbsSyn8
		 (NoAnnotation
	)

happyReduce_8 = happySpecReduce_1  9 happyReduction_8
happyReduction_8 _
	 =  HappyAbsSyn9
		 (Axiom
	)

happyReduce_9 = happySpecReduce_1  9 happyReduction_9
happyReduction_9 _
	 =  HappyAbsSyn9
		 (Lemma
	)

happyReduce_10 = happySpecReduce_1  9 happyReduction_10
happyReduction_10 _
	 =  HappyAbsSyn9
		 (Hypothesis
	)

happyReduce_11 = happySpecReduce_1  9 happyReduction_11
happyReduction_11 _
	 =  HappyAbsSyn9
		 (Definition
	)

happyReduce_12 = happySpecReduce_1  9 happyReduction_12
happyReduction_12 _
	 =  HappyAbsSyn9
		 (Conjecture
	)

happyReduce_13 = happySpecReduce_1  9 happyReduction_13
happyReduction_13 _
	 =  HappyAbsSyn9
		 (Type
	)

happyReduce_14 = happySpecReduce_1  10 happyReduction_14
happyReduction_14 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  11 happyReduction_15
happyReduction_15 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  11 happyReduction_16
happyReduction_16 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  11 happyReduction_17
happyReduction_17 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_17 _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_1  12 happyReduction_18
happyReduction_18 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_1  12 happyReduction_19
happyReduction_19 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  12 happyReduction_20
happyReduction_20 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_3  13 happyReduction_21
happyReduction_21 (HappyAbsSyn11  happy_var_3)
	(HappyAbsSyn32  happy_var_2)
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin happy_var_2 happy_var_1 happy_var_3
	)
happyReduction_21 _ _ _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_1  14 happyReduction_22
happyReduction_22 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_22 _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_1  14 happyReduction_23
happyReduction_23 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_23 _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_1  14 happyReduction_24
happyReduction_24 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_3  15 happyReduction_25
happyReduction_25 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin Or happy_var_1 happy_var_3
	)
happyReduction_25 _ _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_3  15 happyReduction_26
happyReduction_26 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin Or happy_var_1 happy_var_3
	)
happyReduction_26 _ _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_3  16 happyReduction_27
happyReduction_27 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin And happy_var_1 happy_var_3
	)
happyReduction_27 _ _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_3  16 happyReduction_28
happyReduction_28 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin And happy_var_1 happy_var_3
	)
happyReduction_28 _ _ _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_3  17 happyReduction_29
happyReduction_29 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin App happy_var_1 happy_var_3
	)
happyReduction_29 _ _ _  = notHappyAtAll 

happyReduce_30 = happySpecReduce_3  17 happyReduction_30
happyReduction_30 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin App happy_var_1 happy_var_3
	)
happyReduction_30 _ _ _  = notHappyAtAll 

happyReduce_31 = happySpecReduce_1  18 happyReduction_31
happyReduction_31 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_31 _  = notHappyAtAll 

happyReduce_32 = happySpecReduce_1  18 happyReduction_32
happyReduction_32 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_32 _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_1  18 happyReduction_33
happyReduction_33 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_33 _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_3  18 happyReduction_34
happyReduction_34 _
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (happy_var_2
	)
happyReduction_34 _ _ _  = notHappyAtAll 

happyReduce_35 = happyReduce 6 19 happyReduction_35
happyReduction_35 ((HappyAbsSyn11  happy_var_6) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn30  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (Quant happy_var_1 happy_var_3 happy_var_6
	) `HappyStk` happyRest

happyReduce_36 = happySpecReduce_1  20 happyReduction_36
happyReduction_36 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1 : []
	)
happyReduction_36 _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_3  20 happyReduction_37
happyReduction_37 (HappyAbsSyn20  happy_var_3)
	_
	(HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1 : happy_var_3
	)
happyReduction_37 _ _ _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_1  21 happyReduction_38
happyReduction_38 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn21
		 (happy_var_1
	)
happyReduction_38 _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_1  21 happyReduction_39
happyReduction_39 (HappyAbsSyn43  happy_var_1)
	 =  HappyAbsSyn21
		 ((happy_var_1, Nothing)
	)
happyReduction_39 _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_3  22 happyReduction_40
happyReduction_40 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn43  happy_var_1)
	 =  HappyAbsSyn21
		 ((happy_var_1, Just happy_var_3)
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happyReduce 4 23 happyReduction_41
happyReduction_41 (_ `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn33  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (Un happy_var_1 happy_var_3
	) `HappyStk` happyRest

happyReduce_42 = happySpecReduce_3  24 happyReduction_42
happyReduction_42 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Typed happy_var_1 happy_var_3
	)
happyReduction_42 _ _ _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_1  25 happyReduction_43
happyReduction_43 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_43 _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_3  25 happyReduction_44
happyReduction_44 _
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (happy_var_2
	)
happyReduction_44 _ _ _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_1  26 happyReduction_45
happyReduction_45 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_45 _  = notHappyAtAll 

happyReduce_46 = happySpecReduce_1  27 happyReduction_46
happyReduction_46 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_46 _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_1  28 happyReduction_47
happyReduction_47 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_3  29 happyReduction_48
happyReduction_48 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin Map happy_var_1 happy_var_3
	)
happyReduction_48 _ _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_3  29 happyReduction_49
happyReduction_49 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (Bin Map happy_var_1 happy_var_3
	)
happyReduction_49 _ _ _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_1  30 happyReduction_50
happyReduction_50 (HappyAbsSyn30  happy_var_1)
	 =  HappyAbsSyn30
		 (happy_var_1
	)
happyReduction_50 _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_1  30 happyReduction_51
happyReduction_51 _
	 =  HappyAbsSyn30
		 (LambdaAbs
	)

happyReduce_52 = happySpecReduce_1  31 happyReduction_52
happyReduction_52 _
	 =  HappyAbsSyn30
		 (Forall
	)

happyReduce_53 = happySpecReduce_1  31 happyReduction_53
happyReduction_53 _
	 =  HappyAbsSyn30
		 (Exists
	)

happyReduce_54 = happySpecReduce_1  32 happyReduction_54
happyReduction_54 _
	 =  HappyAbsSyn32
		 (Equal
	)

happyReduce_55 = happySpecReduce_2  32 happyReduction_55
happyReduction_55 _
	_
	 =  HappyAbsSyn32
		 (NotEqual
	)

happyReduce_56 = happySpecReduce_1  32 happyReduction_56
happyReduction_56 (HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn32
		 (happy_var_1
	)
happyReduction_56 _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_1  33 happyReduction_57
happyReduction_57 (HappyAbsSyn33  happy_var_1)
	 =  HappyAbsSyn33
		 (happy_var_1
	)
happyReduction_57 _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_2  33 happyReduction_58
happyReduction_58 _
	_
	 =  HappyAbsSyn33
		 (UnExists
	)

happyReduce_59 = happySpecReduce_2  33 happyReduction_59
happyReduction_59 _
	_
	 =  HappyAbsSyn33
		 (UnForall
	)

happyReduce_60 = happySpecReduce_1  33 happyReduction_60
happyReduction_60 _
	 =  HappyAbsSyn33
		 (UnAnd
	)

happyReduce_61 = happySpecReduce_1  33 happyReduction_61
happyReduction_61 _
	 =  HappyAbsSyn33
		 (UnOr
	)

happyReduce_62 = happySpecReduce_2  33 happyReduction_62
happyReduction_62 _
	_
	 =  HappyAbsSyn33
		 (UnImplies
	)

happyReduce_63 = happySpecReduce_3  34 happyReduction_63
happyReduction_63 _
	_
	_
	 =  HappyAbsSyn32
		 (Equiv
	)

happyReduce_64 = happySpecReduce_3  34 happyReduction_64
happyReduction_64 _
	_
	_
	 =  HappyAbsSyn32
		 (NotEquiv
	)

happyReduce_65 = happySpecReduce_2  34 happyReduction_65
happyReduction_65 _
	_
	 =  HappyAbsSyn32
		 (Implies
	)

happyReduce_66 = happySpecReduce_2  34 happyReduction_66
happyReduction_66 _
	_
	 =  HappyAbsSyn32
		 (LeftImplies
	)

happyReduce_67 = happySpecReduce_1  35 happyReduction_67
happyReduction_67 _
	 =  HappyAbsSyn33
		 (Not
	)

happyReduce_68 = happySpecReduce_1  36 happyReduction_68
happyReduction_68 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_68 _  = notHappyAtAll 

happyReduce_69 = happySpecReduce_1  36 happyReduction_69
happyReduction_69 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_69 _  = notHappyAtAll 

happyReduce_70 = happySpecReduce_1  36 happyReduction_70
happyReduction_70 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_70 _  = notHappyAtAll 

happyReduce_71 = happySpecReduce_1  37 happyReduction_71
happyReduction_71 (HappyAbsSyn33  happy_var_1)
	 =  HappyAbsSyn11
		 (UnTerm happy_var_1
	)
happyReduction_71 _  = notHappyAtAll 

happyReduce_72 = happySpecReduce_1  38 happyReduction_72
happyReduction_72 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_72 _  = notHappyAtAll 

happyReduce_73 = happySpecReduce_1  38 happyReduction_73
happyReduction_73 (HappyAbsSyn43  happy_var_1)
	 =  HappyAbsSyn11
		 (Var happy_var_1
	)
happyReduction_73 _  = notHappyAtAll 

happyReduce_74 = happySpecReduce_1  39 happyReduction_74
happyReduction_74 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_74 _  = notHappyAtAll 

happyReduce_75 = happySpecReduce_1  40 happyReduction_75
happyReduction_75 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_75 _  = notHappyAtAll 

happyReduce_76 = happySpecReduce_1  41 happyReduction_76
happyReduction_76 (HappyAbsSyn43  happy_var_1)
	 =  HappyAbsSyn11
		 (Const happy_var_1
	)
happyReduction_76 _  = notHappyAtAll 

happyReduce_77 = happySpecReduce_1  42 happyReduction_77
happyReduction_77 (HappyAbsSyn43  happy_var_1)
	 =  HappyAbsSyn11
		 (DefType happy_var_1
	)
happyReduction_77 _  = notHappyAtAll 

happyReduce_78 = happySpecReduce_2  43 happyReduction_78
happyReduction_78 (HappyTerminal (TKlowercasename happy_var_2))
	_
	 =  HappyAbsSyn43
		 (happy_var_2
	)
happyReduction_78 _ _  = notHappyAtAll 

happyReduce_79 = happySpecReduce_1  44 happyReduction_79
happyReduction_79 (HappyTerminal (TKlowercasename happy_var_1))
	 =  HappyAbsSyn43
		 (happy_var_1
	)
happyReduction_79 _  = notHappyAtAll 

happyReduce_80 = happySpecReduce_1  44 happyReduction_80
happyReduction_80 (HappyTerminal (TKstring happy_var_1))
	 =  HappyAbsSyn43
		 ("'" ++ happy_var_1 ++ "'"
	)
happyReduction_80 _  = notHappyAtAll 

happyReduce_81 = happySpecReduce_1  44 happyReduction_81
happyReduction_81 _
	 =  HappyAbsSyn43
		 ("conjecture"
	)

happyReduce_82 = happySpecReduce_1  45 happyReduction_82
happyReduction_82 (HappyTerminal (TKlowercasename happy_var_1))
	 =  HappyAbsSyn43
		 (happy_var_1
	)
happyReduction_82 _  = notHappyAtAll 

happyReduce_83 = happySpecReduce_1  45 happyReduction_83
happyReduction_83 (HappyTerminal (TKstring happy_var_1))
	 =  HappyAbsSyn43
		 ("'" ++ happy_var_1 ++ "'"
	)
happyReduction_83 _  = notHappyAtAll 

happyReduce_84 = happySpecReduce_1  46 happyReduction_84
happyReduction_84 (HappyTerminal (TKuppercasename happy_var_1))
	 =  HappyAbsSyn43
		 (happy_var_1
	)
happyReduction_84 _  = notHappyAtAll 

happyReduce_85 = happySpecReduce_1  47 happyReduction_85
happyReduction_85 (HappyTerminal (TKstring happy_var_1))
	 =  HappyAbsSyn43
		 (happy_var_1
	)
happyReduction_85 _  = notHappyAtAll 

happyNewToken action sts stk
	= lexer(\tk -> 
	let cont i = action i i tk (HappyState action) sts stk in
	case tk of {
	TKEOF -> action 77 77 tk (HappyState action) sts stk;
	TKoparen -> cont 48;
	TKcparen -> cont 49;
	TKosquare -> cont 50;
	TKcsquare -> cont 51;
	TKcomma -> cont 52;
	TKdot -> cont 53;
	TKvline -> cont 54;
	TKampersand -> cont 55;
	TKat -> cont 56;
	TKcolon -> cont 57;
	TKlangle -> cont 58;
	TKrangle -> cont 59;
	TKbang -> cont 60;
	TKquestion -> cont 61;
	TKequal -> cont 62;
	TKtilde -> cont 63;
	TKdollar -> cont 64;
	TKroof -> cont 65;
	TKthf -> cont 66;
	TKaxiom -> cont 67;
	TKlemma -> cont 68;
	TKhypothesis -> cont 69;
	TKdefinition -> cont 70;
	TKconjecture -> cont 71;
	TKtype -> cont 72;
	TKinclude -> cont 73;
	TKuppercasename happy_dollar_dollar -> cont 74;
	TKlowercasename happy_dollar_dollar -> cont 75;
	TKstring happy_dollar_dollar -> cont 76;
	_ -> happyError' tk
	})

happyError_ tk = happyError' tk

happyThen :: () => P a -> (a -> P b) -> P b
happyThen = (thenP)
happyReturn :: () => a -> P a
happyReturn = (returnP)
happyThen1 = happyThen
happyReturn1 :: () => a -> P a
happyReturn1 = happyReturn
happyError' :: () => (Token) -> P a
happyError' tk = (\token -> happyError) tk

parse = happySomeParser where
  happySomeParser = happyThen (happyParse action_0) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


happyError :: P a 
happyError s l = failP (show l ++ ": Parse error\n") (take 100 s) l
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates/GenericTemplate.hs" #-}








{-# LINE 51 "templates/GenericTemplate.hs" #-}

{-# LINE 61 "templates/GenericTemplate.hs" #-}

{-# LINE 70 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	 (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 148 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
	 sts1@(((st1@(HappyState (action))):(_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk





             new_state = action


happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 246 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail  (1) tk old_st _ stk =
--	trace "failing" $ 
    	happyError_ tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
	action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 311 "templates/GenericTemplate.hs" #-}
{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
