import Lean.Data.KVMap
import Lean.Data.Name
import Lean.Data.Format
import Lean.Compiler.ExternAttr
import Lean.Compiler.IR.Basic
import Lean.Data.HashSet


namespace AML

open Lean

class HasIdx (α : Type) where
  getIdx : α → IR.Index

/-- Element Variable: x -/
structure Evar where
  idx : IR.Index
  deriving Inhabited, Repr

instance : BEq Evar := ⟨fun a b => a.idx == b.idx⟩
instance : ToString Evar := ⟨fun a => "x_" ++ toString a.idx⟩
instance : ToFormat Evar := ⟨fun a => toString a⟩
instance : Hashable Evar := ⟨fun a => hash a.idx⟩
instance : HasIdx Evar := ⟨fun a => a.idx⟩

/-- Set Variable: X -/
structure Svar where
  idx : IR.Index
  deriving Inhabited, Repr

instance : BEq Svar := ⟨fun a b => a.idx == b.idx⟩
instance : ToString Svar := ⟨fun a => "X_" ++ toString a.idx⟩
instance : ToFormat Svar := ⟨fun a => toString a⟩
instance : Hashable Svar := ⟨fun a => hash a.idx⟩
instance : HasIdx Svar := ⟨fun a => a.idx⟩

/-- Constant Symbol: σ -/
structure Symbol where
  idx : IR.Index
  deriving Inhabited, Repr

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
  deriving Repr, BEq

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
def CAEVar (p₁ p₂ : Pattern) : IR.Index := newIdx (p₁.FV.1.insertMany p₂.FV.1)
def CASVar (p₁ p₂ : Pattern) : IR.Index := newIdx (p₁.FV.2.insertMany p₂.FV.2)
def Pattern.isCAEVar (p : Pattern) (e : IR.Index) : Bool := ¬(p.FV.1.contains e)
def Pattern.isCASVar (p : Pattern) (s : IR.Index) : Bool := ¬(p.FV.2.contains s)


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
-- Todo: Pattern Normalization
-- Todo: Prove the Correctness of α-renaming
-- Todo: add toString, toFormat, hashable, BEq, etc.
-- instance : BEq Pattern := ⟨fun a b => Pattern.alphaEqv RBMap.empty RBMap.empty a b⟩

-- #eval (Pattern.exists (Evar.mk 0) (Pattern.evar (Evar.mk 0))) == (Pattern.exists (Evar.mk 1) (Pattern.evar (Evar.mk 1)))

end AML




-- instance : ToString Evar where
--   toString := λ e => match e with | Evar.mk s => s

-- -- Set Variable
-- inductive Svar : Type
--   | mk : String → Svar
--   deriving DecidableEq, Hashable, Repr

-- instance : ToString Svar where
--   toString := λ e => match e with | Svar.mk s => s

-- -- Variable (Auxiliary)
-- inductive Var : Type
--   | e : Evar → Var
--   | s : Svar → Var
--   deriving DecidableEq, Hashable, Repr

-- -- Constant Symbol
-- inductive Symbol : Type
--   | mk : String → Symbol
--   deriving DecidableEq, Repr

-- -- Σ-Patterns
-- inductive Pattern : Type
--   | evar : Evar → Pattern
--   | svar : Svar → Pattern
--   | symbol : Symbol → Pattern
--   | app : Pattern → Pattern → Pattern
--   | bot : Pattern
--   | implies : Pattern → Pattern → Pattern
--   | exists : Evar → Pattern → Pattern
--   | mu : Svar → Pattern → Pattern
--   deriving DecidableEq, Repr

-- -- α-renaming

-- def generate_new_var {α : Type} (e : α) () [ToString α] : String :=
--   match e with
--   | x => (ToString.to_string x) ++ "'"

-- def generate_new_evar (e : Evar) : Evar :=
--   match e with
--   | Evar.mk x => Evar.mk (x ++ "'")

-- def generate_new_svar (e : Svar) : Svar :=
--   match e with
--   | Svar.mk x => Svar.mk (x ++ "'")

-- def renameVar (map : Lean.HashMap Var Var) (e : Var) : Var :=
--   map.find? e |>.getD e

-- def alphaRenameAndFV (map : Map Var Var) (p : Pattern) : (Pattern × Set Var) :=
--   let rec aux (map : Map Var Var) (p : Pattern) : (Pattern × Set Var) :=
--     match p with
--     | evar e => (evar (renameVar map e), {e})
--     | svar s => (svar s, {s})
--     | symbol sym => (symbol sym, ∅)
--     | app p1 p2 =>
--       let (p1', fv1) := aux map p1
--       let (p2', fv2) := aux map p2
--       (app p1' p2', fv1 ∪ fv2)
--     | bot => (bot, ∅)
--     | implies p1 p2 =>
--       let (p1', fv1) := aux map p1
--       let (p2', fv2) := aux map p2
--       (implies p1' p2', fv1 ∪ fv2)
--     | exists e p' =>
--       let new_e := generate_new_evar e
--       let new_map := map.insert e new_e
--       let (p'', fv) := aux new_map p'
--       (exists new_e p'', fv \ {new_e})
--     | mu s p' =>
--       let (p'', fv) := aux map p'
--       (mu s p'', fv)
--   in aux map p

-- -- Free Variables

-- -- def FV (p : Pattern) : Set (Evar × Svar) :=
-- --   match p with
-- --   | Pattern.evar e => {e}
-- --   | Pattern.svar s => {s}
-- --   | Pattern.symbol _ => ∅
-- --   | Pattern.app p1 p2 => FV p1 ∪ FV p2
-- --   | Pattern.bot => ∅
-- --   | Pattern.implies p1 p2 => FV p1 ∪ FV p2
-- --   | Pattern.exists e p' => FV p' \ {e}  -- 移除 e，因为它是绑定的
-- --   | mu s p' => FV p' \ {s}  -- 移除 s，因为它是绑定的
-- --   end

-- -- Constructors
-- -- x
-- def MLevar (x : String) : Pattern := Pattern.evar (Evar.mk x)
-- -- X
-- def MLsvar (x : String) : Pattern := Pattern.svar (Svar.mk x)
-- -- σ
-- def MLsymbol (x : String) : Pattern := Pattern.symbol (Symbol.mk x)
-- -- φ1 φ2
-- def MLapp (x y : Pattern) : Pattern := Pattern.app x y
-- -- ⊥
-- def MLbot : Pattern := Pattern.bot
-- -- φ1 → φ2
-- def MLimplies (x y : Pattern) : Pattern := Pattern.implies x y
-- -- ∃x . φ
-- def MLexists (x : String) (y : Pattern) : Pattern := Pattern.exists (Evar.mk x) y
-- -- μX . φ
-- def MLmu (x : String) (y : Pattern) : Pattern := Pattern.mu (Svar.mk x) y
-- -- Sugars
-- -- ¬φ ≡ φ → ⊥
-- def MLnot (x : Pattern) : Pattern := MLimplies x MLbot
-- -- φ1 ∨ φ2 ≡ ¬φ1 → φ2
-- def MLor (x y : Pattern) : Pattern := MLimplies (MLnot x) y
-- -- φ1 ∧ φ2 ≡ ¬(¬φ1 ∨ ¬φ2)
-- def MLand (x y : Pattern) : Pattern := MLnot (MLor (MLnot x) (MLnot y))
-- -- φ1 ↔ φ2 ≡ (φ1 → φ2) ∧ (φ2 → φ1)
-- def MLiff (x y : Pattern) : Pattern := MLand (MLimplies x y) (MLimplies y x)
-- -- ⊤ ≡ ¬⊥
-- def MLtop : Pattern := MLnot MLbot
-- -- ∀x . φ ≡ ¬∃x . ¬φ
-- def MLforall (x : String) (y : Pattern) : Pattern := MLnot (MLexists x (MLnot y))
-- -- νX . φ ≡ ¬μX . ¬φ[¬X/X] // if φ is positive in X



-- -- Substitution
-- inductive Subst : Type
--   | evar : Evar → Pattern → Subst
--   | svar : Svar → Pattern → Subst
--   deriving DecidableEq, Repr

-- def MLEsubst (x : String) (y : Pattern) : Subst := Subst.evar (Evar.mk x) y
-- def MLSsubst (x : String) (y : Pattern) : Subst := Subst.svar (Svar.mk x) y










def hello := "world"
