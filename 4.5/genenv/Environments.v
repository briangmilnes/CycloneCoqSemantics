Set Implicit Arguments.
Require Import LibKeyType LibValueType LibGenEnv LibVarKey LibTauValue LibEValue.
Require Import LibKappaValue.

Module VarEEnv   := GenEnv VarKey EValue.
Definition Heap  := VarEEnv.env.
Module VarKappa  := GenEnv VarKey KappaValue.
Definition Delta := VarKappa.env.
Module VarTauEnv := GenEnv VarKey TauValue.
Definition Gamma := VarTauEnv.env.

Module VarPathTauEnv := GenEnv VarPathKey TauValue.
