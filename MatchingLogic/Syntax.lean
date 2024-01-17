import Lean.Data.KVMap
import Lean.Data.Name
import Lean.Data.Format
import Lean.Compiler.ExternAttr
import Lean.Compiler.IR.Basic
import Lean.Data.HashSet
import STd.Data.Nat
import Mathlib.Tactic.LibrarySearch

namespace AML

open Lean

class HasIdx (α : Type) where
  getIdx : α → IR.Index

/-- Element Variable: x -/
structure Evar where
  idx : IR.Index
  deriving Inhabited, DecidableEq, Repr

instance : BEq Evar := ⟨fun a b => a.idx == b.idx⟩
instance : ToString Evar := ⟨fun a => "x_" ++ toString a.idx⟩
instance : ToFormat Evar := ⟨fun a => toString a⟩
instance : Hashable Evar := ⟨fun a => hash a.idx⟩
instance : HasIdx Evar := ⟨fun a => a.idx⟩

/-- Set Variable: X -/
structure Svar where
  idx : IR.Index
  deriving Inhabited, Repr, DecidableEq

instance : BEq Svar := ⟨fun a b => a.idx == b.idx⟩
instance : ToString Svar := ⟨fun a => "X_" ++ toString a.idx⟩
instance : ToFormat Svar := ⟨fun a => toString a⟩
instance : Hashable Svar := ⟨fun a => hash a.idx⟩
instance : HasIdx Svar := ⟨fun a => a.idx⟩

/-- Constant Symbol: σ -/
structure Symbol where
  idx : IR.Index
  deriving Inhabited, Repr, DecidableEq

instance : BEq Symbol := ⟨fun a b => a.idx == b.idx⟩
instance : ToString Symbol := ⟨fun a => "σ_" ++ toString a.idx⟩
instance : ToFormat Symbol := ⟨fun a => toString a⟩
instance : Hashable Symbol := ⟨fun a => hash a.idx⟩

/-- Pattern: φ -/
inductive Pattern where
  | evar : Evar → Pattern
  | svar : Svar → Pattern
  | symbol : Symbol → Pattern
  | app : Pattern → Pattern → Pattern
  | bot : Pattern
  | implies : Pattern → Pattern → Pattern
  | exists : Evar → Pattern → Pattern
  | mu : Svar → Pattern → Pattern
  deriving Repr, BEq, DecidableEq

def Pattern.size : Pattern → Nat
  | Pattern.evar _     => Nat.succ Nat.zero
  | Pattern.svar _     => Nat.succ Nat.zero
  | Pattern.symbol _   => Nat.succ Nat.zero
  | Pattern.app p1 p2  => Nat.succ (Nat.add p1.size p2.size)
  | Pattern.bot        => Nat.succ Nat.zero
  | Pattern.implies p1 p2 => Nat.succ (Nat.add p1.size p2.size)
  | Pattern.exists _ p => Nat.succ p.size
  | Pattern.mu _ p     => Nat.succ p.size

/-- Free Variables -/
def Pattern.FV : Pattern → (HashSet IR.Index × HashSet  IR.Index)
  | Pattern.evar e => (HashSet.empty.insert e.idx, HashSet.empty)
  | Pattern.svar s => (HashSet.empty, HashSet.empty.insert s.idx)
  | Pattern.symbol _ => (HashSet.empty, HashSet.empty)
  | Pattern.app p1 p2 =>
    let (fv1, fv2) := p1.FV
    let (fv1', fv2') := p2.FV
    (fv1.insertMany fv1', fv2.insertMany fv2')
  | Pattern.bot => (HashSet.empty, HashSet.empty)
  | Pattern.implies p1 p2 =>
    let (fv1, fv2) := p1.FV
    let (fv1', fv2') := p2.FV
    (fv1.insertMany fv1', fv2.insertMany fv2')
  | Pattern.exists e p' =>
    let (fv1, fv2) := p'.FV
    (fv1.insert e.idx, fv2)
  | Pattern.mu s p' =>
    let (fv1, fv2) := p'.FV
    (fv1, fv2.insert s.idx)

/-- α-renaming -/
def newIdx (V : HashSet IR.Index) : IR.Index :=
  let maxIdx := V.fold (fun max e => if e > max then e else max) 0
  (maxIdx + 1)

-- capture-avoiding variables
def Pattern.CAEVar (p : Pattern) : IR.Index := newIdx p.FV.1
def Pattern.CASVar (p : Pattern) : IR.Index := newIdx p.FV.2
def getCAEVar (p₁ p₂ : Pattern) : IR.Index := newIdx (p₁.FV.1.insertMany p₂.FV.1)
def getCASVar (p₁ p₂ : Pattern) : IR.Index := newIdx (p₁.FV.2.insertMany p₂.FV.2)
def Pattern.isCAEVar (p : Pattern) (e : IR.Index) : Bool := ¬(p.FV.1.contains e)
def Pattern.isCASVar (p : Pattern) (s : IR.Index) : Bool := ¬(p.FV.2.contains s)

def Pattern.renameE (old new :IR.Index) : Pattern → Pattern
  | Pattern.evar e         => if e.idx == old then Pattern.evar (Evar.mk new) else Pattern.evar e
  | Pattern.svar s         => Pattern.svar s
  | Pattern.symbol s       => Pattern.symbol s
  | Pattern.app p₁ p₂      => Pattern.app (p₁.renameE old new) (p₂.renameE old new)
  | Pattern.bot            => Pattern.bot
  | Pattern.implies p₁ p₂  => Pattern.implies (p₁.renameE old new) (p₂.renameE old new)
  | Pattern.exists e p'    => if e.idx == old then Pattern.exists (Evar.mk new) (p'.renameE old new) else Pattern.exists e (p'.renameE old new)
  | Pattern.mu s p'        => Pattern.mu s (p'.renameE old new)
  -- termination_by _ => p.size

def Pattern.alphaRename (ρₑ ρₛ : IR.IndexRenaming) : Pattern → (Pattern × IR.IndexRenaming × IR.IndexRenaming)
  | Pattern.evar e         => let new_e := Evar.mk (ρₑ.find? e.idx |>.getD e.idx)
                              (Pattern.evar new_e, ρₑ, ρₛ)
  | Pattern.svar s         => let new_s := Svar.mk (ρₛ.find? s.idx |>.getD s.idx)
                              (Pattern.svar new_s, ρₑ, ρₛ)
  | Pattern.symbol s       => (Pattern.symbol s, ρₑ, ρₛ)
  | Pattern.app p₁ p₂      => let (p₁', ρ₁ₑ, ρ₁ₛ) := p₁.alphaRename ρₑ ρₛ
                              let (p₂', ρ₂ₑ, ρ₂ₛ) := p₂.alphaRename ρ₁ₑ ρ₁ₛ
                              (Pattern.app p₁' p₂', ρ₂ₑ, ρ₂ₛ)
  | Pattern.bot            => (Pattern.bot, ρₑ, ρₛ)
  | Pattern.implies p₁ p₂  => let (p₁', ρ₁ₑ, ρ₁ₛ) := p₁.alphaRename ρₑ ρₛ
                              let (p₂', ρ₂ₑ, ρ₂ₛ) := p₂.alphaRename ρ₁ₑ ρ₁ₛ
                              (Pattern.implies p₁' p₂', ρ₂ₑ, ρ₂ₛ)
  | Pattern.exists e p'    => let new_e := Evar.mk (ρₑ.find? e.idx |>.getD e.idx)
                              if p'.isCAEVar new_e.idx then
                                let (p'', ρₑ', ρₛ') := p'.alphaRename ρₑ ρₛ
                                (Pattern.exists new_e p'', ρₑ', ρₛ')
                              else
                                let new_e' := Evar.mk p'.CAEVar
                                let (p'', ρₑ', ρₛ') := p'.alphaRename (ρₑ.insert e.idx new_e'.idx) ρₛ
                                (Pattern.exists new_e' p'', ρₑ', ρₛ')
  | Pattern.mu s p'        => let new_s := Svar.mk (ρₛ.find? s.idx |>.getD s.idx)
                              if p'.isCASVar new_s.idx then
                                let (p'', ρₑ', ρₛ') := p'.alphaRename ρₑ ρₛ
                                (Pattern.mu new_s p'', ρₑ', ρₛ')
                              else
                                let new_s' := Svar.mk p'.CASVar
                                let (p'', ρₑ', ρₛ') := p'.alphaRename ρₑ (ρₛ.insert s.idx new_s'.idx)
                                (Pattern.mu new_s' p'', ρₑ', ρₛ')

/-- α-equivalence -/
-- 下面的似乎用处不大
def Var.alphaEqv {α : Type} [HasIdx α] (ρ : IR.IndexRenaming) (v₁ v₂ : α) : Bool :=
  match ρ.find? (HasIdx.getIdx v₁) with
  | some v => v == HasIdx.getIdx v₂
  | none   => HasIdx.getIdx v₁ == HasIdx.getIdx v₂

instance : IR.AlphaEqv Evar := ⟨Var.alphaEqv⟩
instance : IR.AlphaEqv Svar := ⟨Var.alphaEqv⟩

def Pattern.alphaEqv (ρₑ ρₛ : IR.IndexRenaming) : Pattern → Pattern → Bool
  | Pattern.evar e₁,         Pattern.evar e₂         => IR.aeqv ρₑ e₁ e₂
  | Pattern.svar s₁,         Pattern.svar s₂         => IR.aeqv ρₛ s₁ s₂
  | Pattern.symbol s₁,       Pattern.symbol s₂       => s₁ == s₂
  | Pattern.app p₁₁ p₁₂,     Pattern.app p₂₁ p₂₂     => p₁₁.alphaEqv ρₑ ρₛ p₂₁ && p₁₂.alphaEqv ρₑ ρₛ p₂₂
  | Pattern.bot,             Pattern.bot             => true
  | Pattern.implies p₁₁ p₁₂, Pattern.implies p₂₁ p₂₂ => p₁₁.alphaEqv ρₑ ρₛ p₂₁ && p₁₂.alphaEqv ρₑ ρₛ p₂₂
  | Pattern.exists e₁ p₁',   Pattern.exists e₂ p₂'   => IR.aeqv ρₑ e₁ e₂ && p₁'.alphaEqv ρₑ ρₛ p₂'
  | Pattern.mu s₁ p₁',       Pattern.mu s₂ p₂'       => IR.aeqv ρₛ s₁ s₂ && p₁'.alphaEqv ρₑ ρₛ p₂'
  | _, _ => false

-- Todo: 自动获取Index Renaming
-- Todo: Prove the Correctness of α-renaming
-- 上面的似乎用处不大

-- Todo: Pattern Normalization
-- Todo: add toString, toFormat, hashable, BEq, etc.
-- instance : BEq Pattern := ⟨fun a b => Pattern.alphaEqv RBMap.empty RBMap.empty a b⟩

/-- Constructors -/
-- x
def MLevar (x : IR.Index) : Pattern := Pattern.evar (Evar.mk x)
-- X
def MLsvar (x : IR.Index) : Pattern := Pattern.svar (Svar.mk x)
-- σ
def MLsymbol (x : IR.Index) : Pattern := Pattern.symbol (Symbol.mk x)
-- φ1 φ2
def MLapp (x y : Pattern) : Pattern := Pattern.app x y
-- ⊥
def MLbot : Pattern := Pattern.bot
-- φ1 → φ2
def MLimplies (x y : Pattern) : Pattern := Pattern.implies x y
-- ∃x . φ
def MLexists (x : IR.Index) (y : Pattern) : Pattern := Pattern.exists (Evar.mk x) y
-- μX . φ
def MLmu (x : IR.Index) (y : Pattern) : Pattern := Pattern.mu (Svar.mk x) y
-- Sugars
-- ¬φ ≡ φ → ⊥
def MLnot (x : Pattern) : Pattern := MLimplies x MLbot
-- φ1 ∨ φ2 ≡ ¬φ1 → φ2
def MLor (x y : Pattern) : Pattern := MLimplies (MLnot x) y
-- φ1 ∧ φ2 ≡ ¬(¬φ1 ∨ ¬φ2)
def MLand (x y : Pattern) : Pattern := MLnot (MLor (MLnot x) (MLnot y))
-- φ1 ↔ φ2 ≡ (φ1 → φ2) ∧ (φ2 → φ1)
def MLiff (x y : Pattern) : Pattern := MLand (MLimplies x y) (MLimplies y x)
-- ⊤ ≡ ¬⊥
def MLtop : Pattern := MLnot MLbot
-- ∀x . φ ≡ ¬∃x . ¬φ
def MLforall (x : IR.Index) (y : Pattern) : Pattern := MLnot (MLexists x (MLnot y))
-- νX . φ ≡ ¬μX . ¬φ[¬X/X] // if φ is positive in X
-- Todo: positive 判定
def Pattern.negS (X : Svar) : Pattern → Pattern
  | Pattern.evar e         => Pattern.evar e
  | Pattern.svar s         => if s == X then MLnot (MLsvar s.idx) else Pattern.svar s
  | Pattern.symbol s       => Pattern.symbol s
  | Pattern.app p₁ p₂      => Pattern.app (p₁.negS X) (p₂.negS X)
  | Pattern.bot            => Pattern.bot
  | Pattern.implies p₁ p₂  => Pattern.implies (p₁.negS X) (p₂.negS X)
  | Pattern.exists e p'    => Pattern.exists e (p'.negS X)
  | Pattern.mu s p'        => Pattern.mu s (p'.negS X)
def MLnu (x : IR.Index) (y : Pattern) : Pattern := MLnot (MLmu x (MLnot (y.negS (Svar.mk x))))
-- def MLnu (x : IR.Index) (y : Pattern) : Pattern := MLnot (MLmu x (MLnot y))

/-- Substitution -/
abbrev Subst := RBMap IR.Index Pattern compare

def Pattern.subst (ρₑ ρₛ : Subst) (p : Pattern) : Pattern :=
  match p with
  | Pattern.evar e         => match ρₑ.find? e.idx with
                              | some p => p
                              | none   => Pattern.evar e
  | Pattern.svar s         => match ρₛ.find? s.idx with
                              | some p => p
                              | none   => Pattern.svar s
  | Pattern.symbol s       => Pattern.symbol s
  | Pattern.app p₁ p₂      => Pattern.app (p₁.subst ρₑ ρₛ) (p₂.subst ρₑ ρₛ)
  | Pattern.bot            => Pattern.bot
  | Pattern.implies p₁ p₂  => Pattern.implies (p₁.subst ρₑ ρₛ) (p₂.subst ρₑ ρₛ)
  -- Check if capturing-avoid:
  | Pattern.exists e p'    => if ρₑ.contains e.idx then
                                let sbt := ρₑ.find? e.idx |>.getD Pattern.bot
                                let new_e := getCAEVar sbt p'
                                let p'' := p'.renameE e.idx new_e
                                Pattern.exists (Evar.mk new_e) (p''.subst ρₑ ρₛ)
                              else
                                Pattern.exists e (p'.subst ρₑ ρₛ)
  | Pattern.mu s p'        => if ρₛ.contains s.idx then
                                let sbt := ρₛ.find? s.idx |>.getD Pattern.bot
                                let new_s := getCASVar sbt p'
                                let new_p' := p'.alphaRename RBMap.empty (RBMap.empty.insert s.idx new_s) |>.1
                                Pattern.mu (Svar.mk new_s) (new_p'.subst ρₑ ρₛ)
                              else
                                Pattern.mu s (p'.subst ρₑ ρₛ)
  termination_by _ => p.size
  decreasing_by sorry


end AML

def hello := "world"
