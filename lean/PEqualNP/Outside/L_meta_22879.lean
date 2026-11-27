import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22879

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ (n : ℕ) : Circuit :=
  { gates := [
      ⟨GateOp.or, [n + 1, 0]⟩,
      ⟨GateOp.or, [n, 3]⟩,
      ⟨GateOp.or, [n + 2, 2]⟩,
      ⟨GateOp.or, [1, n + 3]⟩,
      ⟨GateOp.or, [2 * n + 3, 2 * n + 2]⟩,
      ⟨GateOp.or, [2 * n + 2, 2 * n]⟩,
      ⟨GateOp.not, [2 * n + 4]⟩,
      ⟨GateOp.and, [2 * n + 1, 2 * n + 6]⟩,
      ⟨GateOp.and, [2 * n + 5, 2 * n + 3]⟩,
      ⟨GateOp.or, [2 * n + 8, 2 * n + 7]⟩
    ]
    output := 2 * n + 9 }

theorem fan (n : ℕ) : FanInTwo (circ n) := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by simp⟩

theorem sz (n : ℕ) : (circ n).size ≤ 10 := by
  simp [circ, Circuit.size]

theorem getD_oneEach_left {n : ℕ} (u v : Fin n) {k : ℕ} (hk : k < n) :
    (oneEach u v).getD k false = decide (u.val = k) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp [Fin.ext_iff, eq_comm]

theorem getD_oneEach_right {n : ℕ} (u v : Fin n) {k : ℕ} (hk : k < n) :
    (oneEach u v).getD (n + k) false = decide (v.val = k) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp [Fin.ext_iff, eq_comm]

theorem getD_append_base {l extra : List Bool} {k : ℕ} (hk : k < l.length) :
    (l ++ extra).getD k false = l.getD k false :=
  List.getD_append l extra false k hk

theorem getD_append_gate {l extra : List Bool} {j : ℕ} :
    (l ++ extra).getD (l.length + j) false = extra.getD j false := by
  rw [List.getD_append_right l extra false (l.length + j) (Nat.le_add_right _ _)]
  simp

theorem rep (n : ℕ) (hn : 5 ≤ n) :
    Represents (fun (u : Fin n) (v : Fin n) =>
      decide ((u.val = 0 ∧ (v.val = 0 ∨ v.val = 3)) ∨
        (u.val = 1 ∧ (v.val = 1 ∨ v.val = 2)) ∨
        (u.val = 2 ∧ v.val = 3) ∨
        (u.val = 3 ∧ (v.val ≤ 1 ∨ 4 ≤ v.val)) ∨
        (4 ≤ u.val ∧ v.val = 0))) (circ n) := by
  intro u v
  set base := oneEach u v
  have hlen : base.length = 2 * n := by
    simp [base, oneEach]
    omega
  have h0 : base.getD 0 false = decide (u.val = 0) := getD_oneEach_left u v (by omega)
  have h1 : base.getD 1 false = decide (u.val = 1) := getD_oneEach_left u v (by omega)
  have h2 : base.getD 2 false = decide (u.val = 2) := getD_oneEach_left u v (by omega)
  have h3 : base.getD 3 false = decide (u.val = 3) := getD_oneEach_left u v (by omega)
  have hv0 : base.getD n false = decide (v.val = 0) := by
    simpa using getD_oneEach_right u v (k := 0) (by omega)
  have hv1 : base.getD (n + 1) false = decide (v.val = 1) := getD_oneEach_right u v (by omega)
  have hv2 : base.getD (n + 2) false = decide (v.val = 2) := getD_oneEach_right u v (by omega)
  have hv3 : base.getD (n + 3) false = decide (v.val = 3) := getD_oneEach_right u v (by omega)
  set a0 := decide (u.val = 0)
  set a1 := decide (u.val = 1)
  set a2 := decide (u.val = 2)
  set a3 := decide (u.val = 3)
  set b0 := decide (v.val = 0)
  set b1 := decide (v.val = 1)
  set b2 := decide (v.val = 2)
  set b3 := decide (v.val = 3)
  have heval : (circ n).eval base =
      ((((b2 || a2) || (b1 || a0)) && (a1 || b3)) ||
        ((b0 || a3) && !((a1 || b3) || (b2 || a2)))) := by
    have hb0 : ∀ extra, (base ++ extra).getD 0 false = a0 := fun _ => by rw [getD_append_base (by omega), h0]
    have hb1 : ∀ extra, (base ++ extra).getD 1 false = a1 := fun _ => by rw [getD_append_base (by omega), h1]
    have hb2 : ∀ extra, (base ++ extra).getD 2 false = a2 := fun _ => by rw [getD_append_base (by omega), h2]
    have hb3 : ∀ extra, (base ++ extra).getD 3 false = a3 := fun _ => by rw [getD_append_base (by omega), h3]
    have hbv0 : ∀ extra, (base ++ extra).getD n false = b0 := fun _ => by rw [getD_append_base (by omega), hv0]
    have hbv1 : ∀ extra, (base ++ extra).getD (n + 1) false = b1 := fun _ => by rw [getD_append_base (by omega), hv1]
    have hbv2 : ∀ extra, (base ++ extra).getD (n + 2) false = b2 := fun _ => by rw [getD_append_base (by omega), hv2]
    have hbv3 : ∀ extra, (base ++ extra).getD (n + 3) false = b3 := fun _ => by rw [getD_append_base (by omega), hv3]
    have hg : ∀ (extra : List Bool) (j : ℕ), (base ++ extra).getD (2 * n + j) false = extra.getD j false :=
      fun extra j => by rw [← hlen, getD_append_gate]
    have hg0 : ∀ (extra : List Bool), (base ++ extra).getD (2 * n) false = extra.getD 0 false :=
      fun extra => by simpa using hg extra 0
    simp only [Circuit.eval, Circuit.wires, circ, List.foldl, GateOp.eval, List.map,
      List.any_cons, List.any_nil, List.all_cons, List.all_nil, List.headD,
      Bool.or_false, Bool.and_true, id_eq, List.append_assoc, List.cons_append, List.nil_append,
      h0, h1, h2, h3, hv0, hv1, hv2, hv3, hb0, hb1, hb2, hb3, hbv0, hbv1, hbv2, hbv3,
      hg, hg0, List.getD_cons_zero, List.getD_cons_succ]
  rw [heval]
  have hu : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 ∨ 4 ≤ u.val := by omega
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ 4 ≤ v.val := by omega
  rcases hu with hu | hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv | hv <;>
    simp [a0, a1, a2, a3, b0, b1, b2, b3, hu, hv, show ∀ x : ℕ, 4 ≤ x → ¬ x = 0 by omega,
      show ∀ x : ℕ, 4 ≤ x → ¬ x = 1 by omega, show ∀ x : ℕ, 4 ≤ x → ¬ x = 2 by omega,
      show ∀ x : ℕ, 4 ≤ x → ¬ x = 3 by omega, show ∀ x : ℕ, 4 ≤ x → ¬ x ≤ 1 by omega]

end PEqualNP.Outside.L_meta_22879

theorem PEqualNP.Outside.L_meta_22879 :
    ∀ n : ℕ, 5 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 0 ∨ v.val = 3)) ∨ (u.val = 1 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ (v.val ≤ 1 ∨ 4 ≤ v.val)) ∨ (4 ≤ u.val ∧ v.val = 0))) C :=
  fun n hn => ⟨PEqualNP.Outside.L_meta_22879.circ n, PEqualNP.Outside.L_meta_22879.fan n,
    PEqualNP.Outside.L_meta_22879.sz n, PEqualNP.Outside.L_meta_22879.rep n hn⟩
