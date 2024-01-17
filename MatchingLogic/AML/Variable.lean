/-
Copyright (c) 2022 Institute for Logic and Data Science (ILDS), Copyright (c) 2024 Jianhong Zhao. All rights reserved.
Released under MIT license as described in the files licenses/LICENSE_ILDS and LICENSE.
Authors: Horațiu Cheval, Jianhong Zhao
-/

import Mathlib.Tactic.LibrarySearch
import Lean.Data.Format
open Lean

namespace AML
-- Variables: (EVar : Type) (SVar : Type)
-- Functions: (getFresh : List EVar → EVar) (getFresh : List SVar → SVar)

@[simp]
def getFresh : List Nat  → Nat
| [] => 0
| .cons x xs => (max x (getFresh xs)) + 1

theorem lt_get_fresh {xs : List Nat} {x : Nat} (h : x ∈ xs) : x < getFresh xs := by
  induction xs with
  | nil => exact Iff.mp List.mem_range h
  | cons hd tl ih =>
    cases h with
    | head =>
      dsimp
      have : x ≤ max x (getFresh tl) := Nat.le_max_left x (getFresh tl)
      exact Nat.lt_succ_of_le this
    | tail _ hmem =>
      dsimp
      specialize ih hmem
      have : getFresh tl ≤ max hd (getFresh tl) := Nat.le_max_right hd (getFresh tl)
      have := Nat.le_trans (Nat.le_of_lt ih) this
      exact Nat.lt_succ_of_le this

theorem get_fresh_is_fresh (xs : List Nat) : getFresh xs ∉ xs :=
  fun h => Nat.lt_irrefl _ $ lt_get_fresh h

theorem get_fresh_is_fresh' (xs : List Nat) : ∀ x ∈ xs, getFresh xs ≠ x := by
  intros x hem h
  have := get_fresh_is_fresh xs
  subst h
  contradiction

@[ext]
structure EVar where
  idx : Nat
deriving DecidableEq, Inhabited, Repr

namespace EVar
  instance : ToString EVar := ⟨fun a => s!"x{a.idx}"⟩
  instance : ToFormat EVar := ⟨fun a => toString a⟩

  theorem evar_eq_def (x y : EVar) : x = y ↔ x.idx = y.idx := by
    apply Iff.intro <;> intros h
    . cases h ; rfl
    . ext ; assumption

  @[simp]
  def getFresh : List EVar → EVar
  | xs => ⟨AML.getFresh <| xs.map EVar.idx⟩

  theorem get_fresh_is_fresh' (xs : List EVar) : ∀ x ∈ xs, getFresh xs ≠ x := by
    intros x hmem h
    rw [evar_eq_def] at h
    have := List.mem_map_of_mem EVar.idx hmem
    exact AML.get_fresh_is_fresh' (xs.map EVar.idx) x.idx this h

  theorem get_fresh_is_fresh (xs : List EVar) : getFresh xs ∉ xs := by
    intros hmem
    exact get_fresh_is_fresh' xs (getFresh xs) hmem rfl

end EVar

@[ext]
structure SVar where
  val : Nat
deriving DecidableEq, Inhabited, Repr

namespace SVar
  instance ToString : ToString SVar := ⟨fun a => s!"X{a.val}"⟩

  theorem svar_eq_def (x y : SVar) : x = y ↔ x.val = y.val := by
    apply Iff.intro <;> intros h
    . cases h ; rfl
    . ext ; assumption

  @[simp]
  def getFresh : List SVar → SVar
  | xs => ⟨AML.getFresh $ xs.map SVar.val⟩

  theorem get_fresh_is_fresh' (xs : List SVar) : ∀ x ∈ xs, getFresh xs ≠ x := by
    intros x hmem h
    rw [svar_eq_def] at h
    have := List.mem_map_of_mem SVar.val hmem
    exact AML.get_fresh_is_fresh' (xs.map SVar.val) x.val this h

  theorem get_fresh_is_fresh (xs : List SVar) : getFresh xs ∉ xs := by
    intros hmem
    exact get_fresh_is_fresh' xs (getFresh xs) hmem rfl

end SVar

end AML
