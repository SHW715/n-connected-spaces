import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected

/- In this file, define [n-connected space](https://ncatlab.org/nlab/show/n-connected+space).
A topological space `X` is `n`-cconected space iff its homotopy group is trivial up to degree `n`.
-/

/-- A topological space `X` is `n`-cconected space iff its homotopy group is trivial up
to degree `n`-/
def is_n_connected (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  Nonempty X ∧ ∀ x : X, ∀ k, k ≤ n → Nonempty (HomotopyGroup.Pi k X x) ∧
    Subsingleton (HomotopyGroup.Pi k X x)

/- the topological space is 0-connected iff it is connected. -/
lemma zero_connected_iff_path_connected (X : Type*) [TopologicalSpace X] :
    is_n_connected X 0 ↔ PathConnectedSpace X := by
  have iff_aux : is_n_connected X 0 ↔
    Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
    unfold is_n_connected
    constructor
    · intro ⟨h₁, h₂⟩
      let x := Classical.choice h₁
      have iso_aux : (HomotopyGroup.Pi 0 X x) ≃ ZerothHomotopy X :=
        HomotopyGroup.pi0EquivZerothHomotopy
      have : Subsingleton (HomotopyGroup.Pi 0 X x) := (h₂ x 0 (Nat.zero_le 0)).2
      exact ⟨Equiv.nonempty iso_aux.symm, Equiv.subsingleton.symm iso_aux⟩
    · intro ⟨h, h'⟩
      have : Nonempty X := (nonempty_quotient_iff _).mp h
      let x := Classical.choice this
      have iso_aux (x : X) : (HomotopyGroup.Pi 0 X x) ≃ ZerothHomotopy X :=
        HomotopyGroup.pi0EquivZerothHomotopy
      constructor
      · exact (nonempty_quotient_iff _).mp h
      · intro x k hk
        have keq : k = 0 := by exact Nat.eq_zero_of_le_zero hk
        rw [keq]
        exact ⟨Equiv.nonempty (iso_aux x), Equiv.subsingleton (iso_aux x)⟩
  rw [pathConnectedSpace_iff_zerothHomotopy]
  exact iff_aux

lemma n_connected_implies_m_connected_of_ge (X : Type*) [TopologicalSpace X] {n m : ℕ}
    (h : m ≤ n) :
    is_n_connected X n → is_n_connected X m :=
  fun h' => ⟨h'.1, fun x k hk => h'.2 x k (.trans hk h )⟩

lemma one_connected_iff_simply_connected (X : Type*) [TopologicalSpace X] :
    is_n_connected X 1 ↔ SimplyConnectedSpace X := by
  constructor
  ·
    intro h
    have : is_n_connected X 0 := n_connected_implies_m_connected_of_ge X zero_le_one h
    rw [simply_connected_iff_loops_nullhomotopic]
    unfold is_n_connected at h
    constructor
    · exact (zero_connected_iff_path_connected X).mp this
    ·
      obtain ⟨h₁, h₂⟩ := h
      -- let x := Classical.choice h₁
      intro x γ
      have iso_aux : HomotopyGroup.Pi 1 X x ≃ FundamentalGroup X x :=
        HomotopyGroup.pi1EquivFundamentalGroup
      obtain subsingleton_aux := (h₂ x 1 (le_refl 1)).2
      obtain aux₀ := Equiv.subsingleton.symm iso_aux
      by_contra hc
      -- have aux : (Path.refl x) ∈ FundamentalGroupoid X := sorry
      -- have aux : ∀ x, Subsingleton (FundamentalGroup X x) := sorry
      --   -- Equiv.subsingleton.symm iso_aux

      sorry
  · intro h
    obtain ⟨path_connected_X, h'⟩ := simply_connected_iff_paths_homotopic.mp h
    constructor
    · exact path_connected_X.nonempty
    · intro x k hk
      by_cases hk₀ : k = 0
      · rw [hk₀]
        have iso_aux : (HomotopyGroup.Pi 0 X x) ≃ ZerothHomotopy X :=
          HomotopyGroup.pi0EquivZerothHomotopy
        rw [pathConnectedSpace_iff_zerothHomotopy] at path_connected_X
        obtain ⟨h₁, h₂⟩ := path_connected_X
        exact ⟨Equiv.nonempty (iso_aux), Equiv.subsingleton (iso_aux)⟩
      · have hk₁ : k = 1 := by omega
        rw [hk₁]
        constructor
        · infer_instance
        · have iso_aux : HomotopyGroup.Pi 1 X x ≃ FundamentalGroup X x :=
            HomotopyGroup.pi1EquivFundamentalGroup
          have subsingleton_aux : Subsingleton (FundamentalGroup X x) := h' _ _
          exact Equiv.subsingleton iso_aux
