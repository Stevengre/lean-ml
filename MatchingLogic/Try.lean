import Mathlib.Tactic.LibrarySearch

def hello := "world"
def world := 1

theorem hello_returns_world : hello = "world" := by
  exact rfl

theorem world_returns_1 : world ≤ 1 := by
  exact Nat.le_refl world

#check Nat.le_refl
