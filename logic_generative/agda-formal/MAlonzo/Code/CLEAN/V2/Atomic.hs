{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.CLEAN.V2.Atomic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma

-- CLEAN.V2.Atomic.ℤ
d_ℤ_6 :: ()
d_ℤ_6 = erased
-- CLEAN.V2.Atomic._+ᵢ_
d__'43''7522'__8 :: Integer -> Integer -> Integer
d__'43''7522'__8 = coe addInt
-- CLEAN.V2.Atomic._-ᵢ_
d__'45''7522'__10 :: Integer -> Integer -> Integer
d__'45''7522'__10 v0 ~v1 = du__'45''7522'__10 v0
du__'45''7522'__10 :: Integer -> Integer
du__'45''7522'__10 v0 = coe v0
-- CLEAN.V2.Atomic._*ᵢ_
d__'42''7522'__16 :: Integer -> Integer -> Integer
d__'42''7522'__16 = coe mulInt
-- CLEAN.V2.Atomic.SemiringType
d_SemiringType_18 = ()
data T_SemiringType_18 = C_L_20 | C_B_22 | C_R_24 | C_Core_26
-- CLEAN.V2.Atomic.SemiringOps
d_SemiringOps_30 a0 = ()
data T_SemiringOps_30
  = C_SemiringOps'46'constructor_115 (AgdaAny -> AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny AgdaAny
-- CLEAN.V2.Atomic.SemiringOps.Carrier
d_Carrier_44 :: T_SemiringOps_30 -> ()
d_Carrier_44 = erased
-- CLEAN.V2.Atomic.SemiringOps.add
d_add_46 :: T_SemiringOps_30 -> AgdaAny -> AgdaAny -> AgdaAny
d_add_46 v0
  = case coe v0 of
      C_SemiringOps'46'constructor_115 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.SemiringOps.mul
d_mul_48 :: T_SemiringOps_30 -> AgdaAny -> AgdaAny -> AgdaAny
d_mul_48 v0
  = case coe v0 of
      C_SemiringOps'46'constructor_115 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.SemiringOps.zeroC
d_zeroC_50 :: T_SemiringOps_30 -> AgdaAny
d_zeroC_50 v0
  = case coe v0 of
      C_SemiringOps'46'constructor_115 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.SemiringOps.oneC
d_oneC_52 :: T_SemiringOps_30 -> AgdaAny
d_oneC_52 v0
  = case coe v0 of
      C_SemiringOps'46'constructor_115 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.bridge-lemma-semiring-type
d_bridge'45'lemma'45'semiring'45'type_56 :: T_SemiringType_18 -> ()
d_bridge'45'lemma'45'semiring'45'type_56 = erased
-- CLEAN.V2.Atomic.L-ops
d_L'45'ops_60 :: T_SemiringOps_30
d_L'45'ops_60
  = coe
      C_SemiringOps'46'constructor_115 (\ v0 v1 -> v0) mulInt
      (0 :: Integer) (1 :: Integer)
-- CLEAN.V2.Atomic.R-ops
d_R'45'ops_66 :: T_SemiringOps_30
d_R'45'ops_66
  = coe
      C_SemiringOps'46'constructor_115 (\ v0 v1 -> v0) mulInt
      (0 :: Integer) (1 :: Integer)
-- CLEAN.V2.Atomic.Core-ops
d_Core'45'ops_72 :: T_SemiringOps_30
d_Core'45'ops_72
  = coe
      C_SemiringOps'46'constructor_115 addInt mulInt (0 :: Integer)
      (1 :: Integer)
-- CLEAN.V2.Atomic.B-ops
d_B'45'ops_74 :: T_SemiringOps_30
d_B'45'ops_74
  = coe
      C_SemiringOps'46'constructor_115 (\ v0 v1 -> v0) (\ v0 v1 -> v0)
      (0 :: Integer) (1 :: Integer)
-- CLEAN.V2.Atomic.SemiringLaws
d_SemiringLaws_88 a0 a1 = ()
data T_SemiringLaws_88 = C_SemiringLaws'46'constructor_1245
-- CLEAN.V2.Atomic._.Carrier
d_Carrier_96 :: T_SemiringOps_30 -> ()
d_Carrier_96 = erased
-- CLEAN.V2.Atomic._.add
d_add_98 :: T_SemiringOps_30 -> AgdaAny -> AgdaAny -> AgdaAny
d_add_98 v0 = coe d_add_46 (coe v0)
-- CLEAN.V2.Atomic._.mul
d_mul_100 :: T_SemiringOps_30 -> AgdaAny -> AgdaAny -> AgdaAny
d_mul_100 v0 = coe d_mul_48 (coe v0)
-- CLEAN.V2.Atomic._.oneC
d_oneC_102 :: T_SemiringOps_30 -> AgdaAny
d_oneC_102 v0 = coe d_oneC_52 (coe v0)
-- CLEAN.V2.Atomic._.zeroC
d_zeroC_104 :: T_SemiringOps_30 -> AgdaAny
d_zeroC_104 v0 = coe d_zeroC_50 (coe v0)
-- CLEAN.V2.Atomic.SemiringLaws._.Carrier
d_Carrier_152 :: T_SemiringOps_30 -> T_SemiringLaws_88 -> ()
d_Carrier_152 = erased
-- CLEAN.V2.Atomic.SemiringLaws._.add
d_add_154 ::
  T_SemiringOps_30 ->
  T_SemiringLaws_88 -> AgdaAny -> AgdaAny -> AgdaAny
d_add_154 v0 ~v1 = du_add_154 v0
du_add_154 :: T_SemiringOps_30 -> AgdaAny -> AgdaAny -> AgdaAny
du_add_154 v0 = coe d_add_46 (coe v0)
-- CLEAN.V2.Atomic.SemiringLaws._.mul
d_mul_156 ::
  T_SemiringOps_30 ->
  T_SemiringLaws_88 -> AgdaAny -> AgdaAny -> AgdaAny
d_mul_156 v0 ~v1 = du_mul_156 v0
du_mul_156 :: T_SemiringOps_30 -> AgdaAny -> AgdaAny -> AgdaAny
du_mul_156 v0 = coe d_mul_48 (coe v0)
-- CLEAN.V2.Atomic.SemiringLaws._.oneC
d_oneC_158 :: T_SemiringOps_30 -> T_SemiringLaws_88 -> AgdaAny
d_oneC_158 v0 ~v1 = du_oneC_158 v0
du_oneC_158 :: T_SemiringOps_30 -> AgdaAny
du_oneC_158 v0 = coe d_oneC_52 (coe v0)
-- CLEAN.V2.Atomic.SemiringLaws._.zeroC
d_zeroC_160 :: T_SemiringOps_30 -> T_SemiringLaws_88 -> AgdaAny
d_zeroC_160 v0 ~v1 = du_zeroC_160 v0
du_zeroC_160 :: T_SemiringOps_30 -> AgdaAny
du_zeroC_160 v0 = coe d_zeroC_50 (coe v0)
-- CLEAN.V2.Atomic.SemiringLaws.add-assoc
d_add'45'assoc_168 ::
  T_SemiringLaws_88 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_add'45'assoc_168 = erased
-- CLEAN.V2.Atomic.SemiringLaws.add-comm
d_add'45'comm_174 ::
  T_SemiringLaws_88 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_add'45'comm_174 = erased
-- CLEAN.V2.Atomic.SemiringLaws.add-zero
d_add'45'zero_178 ::
  T_SemiringLaws_88 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_add'45'zero_178 = erased
-- CLEAN.V2.Atomic.SemiringLaws.mul-assoc
d_mul'45'assoc_186 ::
  T_SemiringLaws_88 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mul'45'assoc_186 = erased
-- CLEAN.V2.Atomic.SemiringLaws.mul-comm
d_mul'45'comm_192 ::
  T_SemiringLaws_88 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mul'45'comm_192 = erased
-- CLEAN.V2.Atomic.SemiringLaws.mul-one
d_mul'45'one_196 ::
  T_SemiringLaws_88 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mul'45'one_196 = erased
-- CLEAN.V2.Atomic.SemiringLaws.distrib
d_distrib_204 ::
  T_SemiringLaws_88 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib_204 = erased
-- CLEAN.V2.Atomic.semiring-laws-L
d_semiring'45'laws'45'L_206
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.semiring-laws-L"
-- CLEAN.V2.Atomic.semiring-laws-R
d_semiring'45'laws'45'R_208
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.semiring-laws-R"
-- CLEAN.V2.Atomic.semiring-laws-B
d_semiring'45'laws'45'B_210
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.semiring-laws-B"
-- CLEAN.V2.Atomic.semiring-laws-Core
d_semiring'45'laws'45'Core_212
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.semiring-laws-Core"
-- CLEAN.V2.Atomic.CarrierL
d_CarrierL_214 :: ()
d_CarrierL_214 = erased
-- CLEAN.V2.Atomic.CarrierR
d_CarrierR_216 :: ()
d_CarrierR_216 = erased
-- CLEAN.V2.Atomic.CarrierB
d_CarrierB_218 :: ()
d_CarrierB_218 = erased
-- CLEAN.V2.Atomic.CarrierCore
d_CarrierCore_220 :: ()
d_CarrierCore_220 = erased
-- CLEAN.V2.Atomic.addL
d_addL_222 :: Integer -> Integer -> Integer
d_addL_222 v0 ~v1 = du_addL_222 v0
du_addL_222 :: Integer -> Integer
du_addL_222 v0 = coe v0
-- CLEAN.V2.Atomic.addR
d_addR_224 :: Integer -> Integer -> Integer
d_addR_224 v0 ~v1 = du_addR_224 v0
du_addR_224 :: Integer -> Integer
du_addR_224 v0 = coe v0
-- CLEAN.V2.Atomic.addB
d_addB_226 :: Integer -> Integer -> Integer
d_addB_226 v0 ~v1 = du_addB_226 v0
du_addB_226 :: Integer -> Integer
du_addB_226 v0 = coe v0
-- CLEAN.V2.Atomic.mulB
d_mulB_228 :: Integer -> Integer -> Integer
d_mulB_228 v0 ~v1 = du_mulB_228 v0
du_mulB_228 :: Integer -> Integer
du_mulB_228 v0 = coe v0
-- CLEAN.V2.Atomic.Moduli
d_Moduli_230 = ()
data T_Moduli_230
  = C_Moduli'46'constructor_2553 (Integer -> Integer)
                                 (Integer -> Integer) (Integer -> Integer) (Integer -> Integer)
                                 (Integer -> Integer) (Integer -> Integer) (Integer -> Integer)
                                 (Integer -> Integer)
                                 (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                                 (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer)
-- CLEAN.V2.Atomic.Moduli.νL⋆
d_νL'8902'_262 :: T_Moduli_230 -> Integer -> Integer
d_νL'8902'_262 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.νR⋆
d_νR'8902'_264 :: T_Moduli_230 -> Integer -> Integer
d_νR'8902'_264 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.ιL⋆
d_ιL'8902'_266 :: T_Moduli_230 -> Integer -> Integer
d_ιL'8902'_266 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.ιR⋆
d_ιR'8902'_268 :: T_Moduli_230 -> Integer -> Integer
d_ιR'8902'_268 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.ad0⋆
d_ad0'8902'_270 :: T_Moduli_230 -> Integer -> Integer
d_ad0'8902'_270 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.ad1⋆
d_ad1'8902'_272 :: T_Moduli_230 -> Integer -> Integer
d_ad1'8902'_272 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.ad2⋆
d_ad2'8902'_274 :: T_Moduli_230 -> Integer -> Integer
d_ad2'8902'_274 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.ad3⋆
d_ad3'8902'_276 :: T_Moduli_230 -> Integer -> Integer
d_ad3'8902'_276 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.dec⋆
d_dec'8902'_284 ::
  T_Moduli_230 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dec'8902'_284 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.Moduli.rec⋆
d_rec'8902'_290 ::
  T_Moduli_230 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_rec'8902'_290 v0
  = case coe v0 of
      C_Moduli'46'constructor_2553 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CanonicalFactorization
d_CanonicalFactorization_292 = ()
data T_CanonicalFactorization_292
  = C_CanonicalFactorization'46'constructor_4547 (Integer -> Integer)
                                                 (Integer -> Integer) (Integer -> Integer)
                                                 (Integer -> Integer) (Integer -> Integer)
                                                 (Integer -> Integer)
-- CLEAN.V2.Atomic.CanonicalFactorization.πL
d_πL_334 :: T_CanonicalFactorization_292 -> Integer -> Integer
d_πL_334 v0
  = case coe v0 of
      C_CanonicalFactorization'46'constructor_4547 v1 v2 v3 v4 v5 v6
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CanonicalFactorization.πR
d_πR_336 :: T_CanonicalFactorization_292 -> Integer -> Integer
d_πR_336 v0
  = case coe v0 of
      C_CanonicalFactorization'46'constructor_4547 v1 v2 v3 v4 v5 v6
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CanonicalFactorization.πCore
d_πCore_338 :: T_CanonicalFactorization_292 -> Integer -> Integer
d_πCore_338 v0
  = case coe v0 of
      C_CanonicalFactorization'46'constructor_4547 v1 v2 v3 v4 v5 v6
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CanonicalFactorization.ιL
d_ιL_340 :: T_CanonicalFactorization_292 -> Integer -> Integer
d_ιL_340 v0
  = case coe v0 of
      C_CanonicalFactorization'46'constructor_4547 v1 v2 v3 v4 v5 v6
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CanonicalFactorization.ιR
d_ιR_342 :: T_CanonicalFactorization_292 -> Integer -> Integer
d_ιR_342 v0
  = case coe v0 of
      C_CanonicalFactorization'46'constructor_4547 v1 v2 v3 v4 v5 v6
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CanonicalFactorization.ιCore
d_ιCore_344 :: T_CanonicalFactorization_292 -> Integer -> Integer
d_ιCore_344 v0
  = case coe v0 of
      C_CanonicalFactorization'46'constructor_4547 v1 v2 v3 v4 v5 v6
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CanonicalFactorization.factorization
d_factorization_348 ::
  T_CanonicalFactorization_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_factorization_348 = erased
-- CLEAN.V2.Atomic.CanonicalFactorization.orthogonality-LR
d_orthogonality'45'LR_352 ::
  T_CanonicalFactorization_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orthogonality'45'LR_352 = erased
-- CLEAN.V2.Atomic.CanonicalFactorization.orthogonality-RL
d_orthogonality'45'RL_356 ::
  T_CanonicalFactorization_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orthogonality'45'RL_356 = erased
-- CLEAN.V2.Atomic.CanonicalFactorization.orthogonality-LCore
d_orthogonality'45'LCore_360 ::
  T_CanonicalFactorization_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orthogonality'45'LCore_360 = erased
-- CLEAN.V2.Atomic.CanonicalFactorization.orthogonality-RCore
d_orthogonality'45'RCore_364 ::
  T_CanonicalFactorization_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orthogonality'45'RCore_364 = erased
-- CLEAN.V2.Atomic.CanonicalFactorization.orthogonality-CoreL
d_orthogonality'45'CoreL_368 ::
  T_CanonicalFactorization_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orthogonality'45'CoreL_368 = erased
-- CLEAN.V2.Atomic.CanonicalFactorization.orthogonality-CoreR
d_orthogonality'45'CoreR_372 ::
  T_CanonicalFactorization_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_orthogonality'45'CoreR_372 = erased
-- CLEAN.V2.Atomic.MonoidSemiringStructure
d_MonoidSemiringStructure_374 = ()
data T_MonoidSemiringStructure_374
  = C_MonoidSemiringStructure'46'constructor_7887
-- CLEAN.V2.Atomic.MonoidSemiringStructure.header-monoid
d_header'45'monoid_422 :: T_MonoidSemiringStructure_374 -> ()
d_header'45'monoid_422 = erased
-- CLEAN.V2.Atomic.MonoidSemiringStructure.bulk-semiring
d_bulk'45'semiring_424 :: T_MonoidSemiringStructure_374 -> ()
d_bulk'45'semiring_424 = erased
-- CLEAN.V2.Atomic.MonoidSemiringStructure.header-multiplication
d_header'45'multiplication_442 ::
  T_MonoidSemiringStructure_374 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_header'45'multiplication_442 = erased
-- CLEAN.V2.Atomic.MonoidSemiringStructure.header-addition
d_header'45'addition_460 ::
  T_MonoidSemiringStructure_374 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_header'45'addition_460 = erased
-- CLEAN.V2.Atomic.MonoidSemiringStructure.observer-homomorphism
d_observer'45'homomorphism_466 ::
  T_MonoidSemiringStructure_374 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_observer'45'homomorphism_466 = erased
-- CLEAN.V2.Atomic.ProfoundExpLog
d_ProfoundExpLog_468 = ()
data T_ProfoundExpLog_468
  = C_ProfoundExpLog'46'constructor_14633 Integer Integer Integer
                                          Integer
                                          (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                                          (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer)
-- CLEAN.V2.Atomic.ProfoundExpLog.φ
d_φ_538 :: T_ProfoundExpLog_468 -> Integer
d_φ_538 v0
  = case coe v0 of
      C_ProfoundExpLog'46'constructor_14633 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundExpLog.z
d_z_540 :: T_ProfoundExpLog_468 -> Integer
d_z_540 v0
  = case coe v0 of
      C_ProfoundExpLog'46'constructor_14633 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundExpLog.z̄
d_z'772'_542 :: T_ProfoundExpLog_468 -> Integer
d_z'772'_542 v0
  = case coe v0 of
      C_ProfoundExpLog'46'constructor_14633 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundExpLog.Λ
d_Λ_544 :: T_ProfoundExpLog_468 -> Integer
d_Λ_544 v0
  = case coe v0 of
      C_ProfoundExpLog'46'constructor_14633 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundExpLog.dec-canonical
d_dec'45'canonical_552 ::
  T_ProfoundExpLog_468 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dec'45'canonical_552 v0
  = case coe v0 of
      C_ProfoundExpLog'46'constructor_14633 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundExpLog.rec-canonical
d_rec'45'canonical_560 ::
  T_ProfoundExpLog_468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_rec'45'canonical_560 v0
  = case coe v0 of
      C_ProfoundExpLog'46'constructor_14633 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundExpLog.iso-left
d_iso'45'left_564 ::
  T_ProfoundExpLog_468 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iso'45'left_564 = erased
-- CLEAN.V2.Atomic.ProfoundExpLog.iso-right
d_iso'45'right_574 ::
  T_ProfoundExpLog_468 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iso'45'right_574 = erased
-- CLEAN.V2.Atomic.ProfoundExpLog.mult-compat
d_mult'45'compat_600 ::
  T_ProfoundExpLog_468 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mult'45'compat_600 = erased
-- CLEAN.V2.Atomic.ProfoundExpLog.header-factoring
d_header'45'factoring_604 ::
  T_ProfoundExpLog_468 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_header'45'factoring_604 = erased
-- CLEAN.V2.Atomic.ProfoundExpLog.power-φ
d_power'45'φ_606 :: T_ProfoundExpLog_468 -> Integer -> Integer
d_power'45'φ_606 ~v0 ~v1 = du_power'45'φ_606
du_power'45'φ_606 :: Integer
du_power'45'φ_606 = coe (1 :: Integer)
-- CLEAN.V2.Atomic.ProfoundExpLog.power-z
d_power'45'z_610 :: T_ProfoundExpLog_468 -> Integer -> Integer
d_power'45'z_610 ~v0 v1 = du_power'45'z_610 v1
du_power'45'z_610 :: Integer -> Integer
du_power'45'z_610 v0 = coe seq (coe v0) (coe (1 :: Integer))
-- CLEAN.V2.Atomic.ProfoundExpLog.power-z̄
d_power'45'z'772'_614 :: T_ProfoundExpLog_468 -> Integer -> Integer
d_power'45'z'772'_614 ~v0 v1 = du_power'45'z'772'_614 v1
du_power'45'z'772'_614 :: Integer -> Integer
du_power'45'z'772'_614 v0 = coe seq (coe v0) (coe (1 :: Integer))
-- CLEAN.V2.Atomic.AuxiliaryTransporter
d_AuxiliaryTransporter_618 = ()
newtype T_AuxiliaryTransporter_618
  = C_AuxiliaryTransporter'46'constructor_15671 (Integer ->
                                                 Integer -> Integer -> Integer -> Integer)
-- CLEAN.V2.Atomic.AuxiliaryTransporter.transporter
d_transporter_644 ::
  T_AuxiliaryTransporter_618 ->
  Integer -> Integer -> Integer -> Integer -> Integer
d_transporter_644 v0
  = case coe v0 of
      C_AuxiliaryTransporter'46'constructor_15671 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.AuxiliaryTransporter.header-preservation
d_header'45'preservation_656 ::
  T_AuxiliaryTransporter_618 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_header'45'preservation_656 = erased
-- CLEAN.V2.Atomic.AuxiliaryTransporter.centrality
d_centrality_666 ::
  T_AuxiliaryTransporter_618 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_centrality_666 = erased
-- CLEAN.V2.Atomic.ProfoundBraiding
d_ProfoundBraiding_668 = ()
data T_ProfoundBraiding_668
  = C_ProfoundBraiding'46'constructor_16809 (Integer -> Integer)
                                            (Integer -> Integer) (Integer -> Integer)
                                            (Integer -> Integer)
-- CLEAN.V2.Atomic.ProfoundBraiding.ad₀
d_ad'8320'_708 :: T_ProfoundBraiding_668 -> Integer -> Integer
d_ad'8320'_708 v0
  = case coe v0 of
      C_ProfoundBraiding'46'constructor_16809 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundBraiding.ad₁
d_ad'8321'_710 :: T_ProfoundBraiding_668 -> Integer -> Integer
d_ad'8321'_710 v0
  = case coe v0 of
      C_ProfoundBraiding'46'constructor_16809 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundBraiding.ad₂
d_ad'8322'_712 :: T_ProfoundBraiding_668 -> Integer -> Integer
d_ad'8322'_712 v0
  = case coe v0 of
      C_ProfoundBraiding'46'constructor_16809 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundBraiding.ad₃
d_ad'8323'_714 :: T_ProfoundBraiding_668 -> Integer -> Integer
d_ad'8323'_714 v0
  = case coe v0 of
      C_ProfoundBraiding'46'constructor_16809 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ProfoundBraiding.yang-baxter-01
d_yang'45'baxter'45'01_718 ::
  T_ProfoundBraiding_668 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_yang'45'baxter'45'01_718 = erased
-- CLEAN.V2.Atomic.ProfoundBraiding.yang-baxter-12
d_yang'45'baxter'45'12_722 ::
  T_ProfoundBraiding_668 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_yang'45'baxter'45'12_722 = erased
-- CLEAN.V2.Atomic.ProfoundBraiding.yang-baxter-23
d_yang'45'baxter'45'23_726 ::
  T_ProfoundBraiding_668 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_yang'45'baxter'45'23_726 = erased
-- CLEAN.V2.Atomic.ProfoundBraiding.comm-02
d_comm'45'02_730 ::
  T_ProfoundBraiding_668 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm'45'02_730 = erased
-- CLEAN.V2.Atomic.ProfoundBraiding.comm-03
d_comm'45'03_734 ::
  T_ProfoundBraiding_668 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm'45'03_734 = erased
-- CLEAN.V2.Atomic.ProfoundBraiding.comm-13
d_comm'45'13_738 ::
  T_ProfoundBraiding_668 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm'45'13_738 = erased
-- CLEAN.V2.Atomic.ProfoundBraiding.exp-log-respect
d_exp'45'log'45'respect_744 ::
  T_ProfoundBraiding_668 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exp'45'log'45'respect_744 = erased
-- CLEAN.V2.Atomic.ModuliDrivenFeynman
d_ModuliDrivenFeynman_746 = ()
data T_ModuliDrivenFeynman_746
  = C_ModuliDrivenFeynman'46'constructor_17597 T_AuxiliaryTransporter_618
                                               (Integer -> Integer) (Integer -> Integer)
                                               (Integer -> Integer) (Integer -> Integer)
                                               (Integer -> Integer) (Integer -> Integer)
                                               (Integer -> Integer) (Integer -> Integer)
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.transporter
d_transporter_772 ::
  T_ModuliDrivenFeynman_746 -> T_AuxiliaryTransporter_618
d_transporter_772 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.modulated-ad₀
d_modulated'45'ad'8320'_774 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_modulated'45'ad'8320'_774 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.modulated-ad₁
d_modulated'45'ad'8321'_776 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_modulated'45'ad'8321'_776 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.modulated-ad₂
d_modulated'45'ad'8322'_778 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_modulated'45'ad'8322'_778 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.modulated-ad₃
d_modulated'45'ad'8323'_780 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_modulated'45'ad'8323'_780 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.increment-phase
d_increment'45'phase_782 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_increment'45'phase_782 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.increment-scale-z
d_increment'45'scale'45'z_784 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_increment'45'scale'45'z_784 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.increment-scale-zbar
d_increment'45'scale'45'zbar_786 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_increment'45'scale'45'zbar_786 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.step-weight
d_step'45'weight_788 ::
  T_ModuliDrivenFeynman_746 -> Integer -> Integer
d_step'45'weight_788 v0
  = case coe v0 of
      C_ModuliDrivenFeynman'46'constructor_17597 v1 v2 v3 v4 v5 v6 v7 v8 v9
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ModuliDrivenFeynman.modulated-composition
d_modulated'45'composition_794 ::
  T_ModuliDrivenFeynman_746 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulated'45'composition_794 = erased
-- CLEAN.V2.Atomic.ConjugationAuxiliarySwap
d_ConjugationAuxiliarySwap_796 = ()
data T_ConjugationAuxiliarySwap_796
  = C_ConjugationAuxiliarySwap'46'constructor_18231 (Integer ->
                                                     Integer)
                                                    (Integer -> Integer) (Integer -> Integer)
-- CLEAN.V2.Atomic.ConjugationAuxiliarySwap.starB
d_starB_818 :: T_ConjugationAuxiliarySwap_796 -> Integer -> Integer
d_starB_818 v0
  = case coe v0 of
      C_ConjugationAuxiliarySwap'46'constructor_18231 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ConjugationAuxiliarySwap.starL
d_starL_820 :: T_ConjugationAuxiliarySwap_796 -> Integer -> Integer
d_starL_820 v0
  = case coe v0 of
      C_ConjugationAuxiliarySwap'46'constructor_18231 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ConjugationAuxiliarySwap.starR
d_starR_822 :: T_ConjugationAuxiliarySwap_796 -> Integer -> Integer
d_starR_822 v0
  = case coe v0 of
      C_ConjugationAuxiliarySwap'46'constructor_18231 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ConjugationAuxiliarySwap.anti-involution
d_anti'45'involution_826 ::
  T_ConjugationAuxiliarySwap_796 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anti'45'involution_826 = erased
-- CLEAN.V2.Atomic.ConjugationAuxiliarySwap.embedding-compatibility
d_embedding'45'compatibility_832 ::
  T_ConjugationAuxiliarySwap_796 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_embedding'45'compatibility_832 = erased
-- CLEAN.V2.Atomic.ConjugationAuxiliarySwap.auxiliary-swap
d_auxiliary'45'swap_836 ::
  T_ConjugationAuxiliarySwap_796 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_auxiliary'45'swap_836 = erased
-- CLEAN.V2.Atomic.moduli-default
d_moduli'45'default_838 :: T_Moduli_230
d_moduli'45'default_838
  = coe
      C_Moduli'46'constructor_2553 (coe (\ v0 -> v0)) (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 -> v0))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                    (coe v0)))))
      (coe
         (\ v0 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))))
-- CLEAN.V2.Atomic.CentralScalars
d_CentralScalars_860 = ()
data T_CentralScalars_860
  = C_CentralScalars'46'constructor_18497 T_SemiringOps_30
                                          T_SemiringOps_30 T_SemiringOps_30 T_SemiringOps_30
-- CLEAN.V2.Atomic.CentralScalars.φ
d_φ_870 :: T_CentralScalars_860 -> T_SemiringOps_30
d_φ_870 v0
  = case coe v0 of
      C_CentralScalars'46'constructor_18497 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CentralScalars.z
d_z_872 :: T_CentralScalars_860 -> T_SemiringOps_30
d_z_872 v0
  = case coe v0 of
      C_CentralScalars'46'constructor_18497 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CentralScalars.z̄
d_z'772'_874 :: T_CentralScalars_860 -> T_SemiringOps_30
d_z'772'_874 v0
  = case coe v0 of
      C_CentralScalars'46'constructor_18497 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.CentralScalars.Λ
d_Λ_876 :: T_CentralScalars_860 -> T_SemiringOps_30
d_Λ_876 v0
  = case coe v0 of
      C_CentralScalars'46'constructor_18497 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.φ-central
d_φ'45'central_882
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.\966-central"
-- CLEAN.V2.Atomic.z-central
d_z'45'central_888
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.z-central"
-- CLEAN.V2.Atomic.z̄-central
d_z'772''45'central_894
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.z\772-central"
-- CLEAN.V2.Atomic.Λ-central
d_Λ'45'central_900
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.\923-central"
-- CLEAN.V2.Atomic.φ-unit
d_φ'45'unit_906
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.\966-unit"
-- CLEAN.V2.Atomic.z-unit
d_z'45'unit_912
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.z-unit"
-- CLEAN.V2.Atomic.z̄-unit
d_z'772''45'unit_918
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.z\772-unit"
-- CLEAN.V2.Atomic.Λ-unit
d_Λ'45'unit_924
  = error
      "MAlonzo Runtime Error: postulate evaluated: CLEAN.V2.Atomic.\923-unit"
-- CLEAN.V2.Atomic.ObserversEmbeddings
d_ObserversEmbeddings_926 = ()
data T_ObserversEmbeddings_926
  = C_ObserversEmbeddings'46'constructor_22095 (Integer -> Integer)
                                               (Integer -> Integer) (Integer -> Integer)
                                               (Integer -> Integer)
-- CLEAN.V2.Atomic.ObserversEmbeddings.νL
d_νL_988 :: T_ObserversEmbeddings_926 -> Integer -> Integer
d_νL_988 v0
  = case coe v0 of
      C_ObserversEmbeddings'46'constructor_22095 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ObserversEmbeddings.νR
d_νR_990 :: T_ObserversEmbeddings_926 -> Integer -> Integer
d_νR_990 v0
  = case coe v0 of
      C_ObserversEmbeddings'46'constructor_22095 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ObserversEmbeddings.ιL
d_ιL_992 :: T_ObserversEmbeddings_926 -> Integer -> Integer
d_ιL_992 v0
  = case coe v0 of
      C_ObserversEmbeddings'46'constructor_22095 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ObserversEmbeddings.ιR
d_ιR_994 :: T_ObserversEmbeddings_926 -> Integer -> Integer
d_ιR_994 v0
  = case coe v0 of
      C_ObserversEmbeddings'46'constructor_22095 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ObserversEmbeddings.retractionL
d_retractionL_998 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_retractionL_998 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.retractionR
d_retractionR_1002 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_retractionR_1002 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.homL-add
d_homL'45'add_1008 ::
  T_ObserversEmbeddings_926 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_homL'45'add_1008 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.homR-add
d_homR'45'add_1014 ::
  T_ObserversEmbeddings_926 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_homR'45'add_1014 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.zero-pres-L
d_zero'45'pres'45'L_1016 ::
  T_ObserversEmbeddings_926 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'45'pres'45'L_1016 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.zero-pres-R
d_zero'45'pres'45'R_1018 ::
  T_ObserversEmbeddings_926 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'45'pres'45'R_1018 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.one-pres-L
d_one'45'pres'45'L_1020 ::
  T_ObserversEmbeddings_926 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_one'45'pres'45'L_1020 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.one-pres-R
d_one'45'pres'45'R_1022 ::
  T_ObserversEmbeddings_926 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_one'45'pres'45'R_1022 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.projectorL-idem
d_projectorL'45'idem_1026 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectorL'45'idem_1026 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.projectorR-idem
d_projectorR'45'idem_1030 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectorR'45'idem_1030 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.bulk=boundaries-L
d_bulk'61'boundaries'45'L_1034 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bulk'61'boundaries'45'L_1034 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.bulk=boundaries-R
d_bulk'61'boundaries'45'R_1038 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bulk'61'boundaries'45'R_1038 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.residual-L
d_residual'45'L_1042 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_residual'45'L_1042 = erased
-- CLEAN.V2.Atomic.ObserversEmbeddings.residual-R
d_residual'45'R_1046 ::
  T_ObserversEmbeddings_926 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_residual'45'R_1046 = erased
-- CLEAN.V2.Atomic.observers-embeddings-bridge
d_observers'45'embeddings'45'bridge_1048 ::
  T_ObserversEmbeddings_926
d_observers'45'embeddings'45'bridge_1048
  = coe
      C_ObserversEmbeddings'46'constructor_22095 (\ v0 -> v0)
      (\ v0 -> v0) (\ v0 -> v0) (\ v0 -> v0)
-- CLEAN.V2.Atomic.BraidedOperators
d_BraidedOperators_1076 = ()
data T_BraidedOperators_1076
  = C_BraidedOperators'46'constructor_23359 (Integer -> Integer)
                                            (Integer -> Integer) (Integer -> Integer)
                                            (Integer -> Integer)
-- CLEAN.V2.Atomic.BraidedOperators.ad₀
d_ad'8320'_1090 :: T_BraidedOperators_1076 -> Integer -> Integer
d_ad'8320'_1090 v0
  = case coe v0 of
      C_BraidedOperators'46'constructor_23359 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.BraidedOperators.ad₁
d_ad'8321'_1092 :: T_BraidedOperators_1076 -> Integer -> Integer
d_ad'8321'_1092 v0
  = case coe v0 of
      C_BraidedOperators'46'constructor_23359 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.BraidedOperators.ad₂
d_ad'8322'_1094 :: T_BraidedOperators_1076 -> Integer -> Integer
d_ad'8322'_1094 v0
  = case coe v0 of
      C_BraidedOperators'46'constructor_23359 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.BraidedOperators.ad₃
d_ad'8323'_1096 :: T_BraidedOperators_1076 -> Integer -> Integer
d_ad'8323'_1096 v0
  = case coe v0 of
      C_BraidedOperators'46'constructor_23359 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.BraidedOperators.yang-baxter-hex
d_yang'45'baxter'45'hex_1100 ::
  T_BraidedOperators_1076 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_yang'45'baxter'45'hex_1100 = erased
-- CLEAN.V2.Atomic.braided-operators-bridge
d_braided'45'operators'45'bridge_1102 :: T_BraidedOperators_1076
d_braided'45'operators'45'bridge_1102
  = coe
      C_BraidedOperators'46'constructor_23359 (\ v0 -> v0) (\ v0 -> v0)
      (\ v0 -> v0) (\ v0 -> v0)
-- CLEAN.V2.Atomic.Decomp
d_Decomp_1108 :: ()
d_Decomp_1108 = erased
-- CLEAN.V2.Atomic.ExpLogIsomorphism
d_ExpLogIsomorphism_1116 = ()
data T_ExpLogIsomorphism_1116
  = C_ExpLogIsomorphism'46'constructor_26665 (Integer ->
                                              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                                             (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer)
                                             (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- CLEAN.V2.Atomic.ExpLogIsomorphism.dec-z-z̄
d_dec'45'z'45'z'772'_1160 ::
  T_ExpLogIsomorphism_1116 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dec'45'z'45'z'772'_1160 v0
  = case coe v0 of
      C_ExpLogIsomorphism'46'constructor_26665 v1 v2 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ExpLogIsomorphism.rec-z-z̄
d_rec'45'z'45'z'772'_1166 ::
  T_ExpLogIsomorphism_1116 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_rec'45'z'45'z'772'_1166 v0
  = case coe v0 of
      C_ExpLogIsomorphism'46'constructor_26665 v1 v2 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ExpLogIsomorphism.iso-left
d_iso'45'left_1172 ::
  T_ExpLogIsomorphism_1116 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iso'45'left_1172 = erased
-- CLEAN.V2.Atomic.ExpLogIsomorphism.iso-right
d_iso'45'right_1182 ::
  T_ExpLogIsomorphism_1116 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iso'45'right_1182 = erased
-- CLEAN.V2.Atomic.ExpLogIsomorphism.multiplicative-compat
d_multiplicative'45'compat_1188 ::
  T_ExpLogIsomorphism_1116 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_multiplicative'45'compat_1188 = erased
-- CLEAN.V2.Atomic.ExpLogIsomorphism.nfB
d_nfB_1194 ::
  T_ExpLogIsomorphism_1116 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nfB_1194 v0
  = case coe v0 of
      C_ExpLogIsomorphism'46'constructor_26665 v1 v2 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.ExpLogIsomorphism.nfB-law
d_nfB'45'law_1200 ::
  T_ExpLogIsomorphism_1116 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nfB'45'law_1200 = erased
-- CLEAN.V2.Atomic.exp-log-isomorphism-bridge
d_exp'45'log'45'isomorphism'45'bridge_1202 ::
  T_ExpLogIsomorphism_1116
d_exp'45'log'45'isomorphism'45'bridge_1202
  = coe
      C_ExpLogIsomorphism'46'constructor_26665
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                 (coe v0))))
      (\ v0 ->
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
              (coe v0)))
-- CLEAN.V2.Atomic.V2Foundation
d_V2Foundation_1226 = ()
data T_V2Foundation_1226
  = C_V2Foundation'46'constructor_27293 T_SemiringOps_30
                                        T_SemiringOps_30 T_SemiringOps_30 T_SemiringOps_30
                                        T_ObserversEmbeddings_926 T_BraidedOperators_1076
                                        T_ExpLogIsomorphism_1116
-- CLEAN.V2.Atomic.V2Foundation.semiringL
d_semiringL_1242 :: T_V2Foundation_1226 -> T_SemiringOps_30
d_semiringL_1242 v0
  = case coe v0 of
      C_V2Foundation'46'constructor_27293 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V2Foundation.semiringR
d_semiringR_1244 :: T_V2Foundation_1226 -> T_SemiringOps_30
d_semiringR_1244 v0
  = case coe v0 of
      C_V2Foundation'46'constructor_27293 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V2Foundation.semiringB
d_semiringB_1246 :: T_V2Foundation_1226 -> T_SemiringOps_30
d_semiringB_1246 v0
  = case coe v0 of
      C_V2Foundation'46'constructor_27293 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V2Foundation.semiringCore
d_semiringCore_1248 :: T_V2Foundation_1226 -> T_SemiringOps_30
d_semiringCore_1248 v0
  = case coe v0 of
      C_V2Foundation'46'constructor_27293 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V2Foundation.observers
d_observers_1250 ::
  T_V2Foundation_1226 -> T_ObserversEmbeddings_926
d_observers_1250 v0
  = case coe v0 of
      C_V2Foundation'46'constructor_27293 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V2Foundation.braiding
d_braiding_1252 :: T_V2Foundation_1226 -> T_BraidedOperators_1076
d_braiding_1252 v0
  = case coe v0 of
      C_V2Foundation'46'constructor_27293 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V2Foundation.expLog
d_expLog_1254 :: T_V2Foundation_1226 -> T_ExpLogIsomorphism_1116
d_expLog_1254 v0
  = case coe v0 of
      C_V2Foundation'46'constructor_27293 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V10Machine
d_V10Machine_1256 = ()
data T_V10Machine_1256
  = C_V10Machine'46'constructor_27459 T_ObserversEmbeddings_926
                                      T_BraidedOperators_1076 T_ExpLogIsomorphism_1116
-- CLEAN.V2.Atomic.V10Machine.observers
d_observers_1264 :: T_V10Machine_1256 -> T_ObserversEmbeddings_926
d_observers_1264 v0
  = case coe v0 of
      C_V10Machine'46'constructor_27459 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V10Machine.braiding
d_braiding_1266 :: T_V10Machine_1256 -> T_BraidedOperators_1076
d_braiding_1266 v0
  = case coe v0 of
      C_V10Machine'46'constructor_27459 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.V10Machine.expLog
d_expLog_1268 :: T_V10Machine_1256 -> T_ExpLogIsomorphism_1116
d_expLog_1268 v0
  = case coe v0 of
      C_V10Machine'46'constructor_27459 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- CLEAN.V2.Atomic.v2-foundation-default
d_v2'45'foundation'45'default_1270 :: T_V2Foundation_1226
d_v2'45'foundation'45'default_1270
  = coe
      C_V2Foundation'46'constructor_27293 (coe d_L'45'ops_60)
      (coe d_R'45'ops_66) (coe d_B'45'ops_74) (coe d_Core'45'ops_72)
      (coe d_observers'45'embeddings'45'bridge_1048)
      (coe d_braided'45'operators'45'bridge_1102)
      (coe d_exp'45'log'45'isomorphism'45'bridge_1202)
-- CLEAN.V2.Atomic.v10-machine-default
d_v10'45'machine'45'default_1272 :: T_V10Machine_1256
d_v10'45'machine'45'default_1272
  = coe
      C_V10Machine'46'constructor_27459
      (coe d_observers'45'embeddings'45'bridge_1048)
      (coe d_braided'45'operators'45'bridge_1102)
      (coe d_exp'45'log'45'isomorphism'45'bridge_1202)
