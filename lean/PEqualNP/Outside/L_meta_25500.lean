import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25491
import PEqualNP.Outside.L_lib_370
import PEqualNP.MetaComplexity.Helpers.RepPath

namespace PEqualNP.Outside.L_meta_25500_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def lit {r h : ℕ} (b : Fin r → Fin h → Bool) (x : Fin r) (c : Fin (2 * h)) : Bool :=
  b x ⟨c.val / 2, (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).2
    (lt_of_lt_of_eq c.isLt (Nat.mul_comm 2 h))⟩ == c.val.testBit 0

def col {h : ℕ} (j : Fin h) (e : Bool) : Fin (2 * h) :=
  ⟨2 * j.val + e.toNat, by
    have := j.isLt
    cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩

theorem lit_col {r h : ℕ} (b : Fin r → Fin h → Bool) (x : Fin r) (j : Fin h) (e : Bool) :
    lit b x (col j e) = (b x j == e) := by
  have h1 : (2 * j.val + e.toNat) / 2 = j.val := by
    cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have h2 : (2 * j.val + e.toNat).testBit 0 = e := by
    rw [Nat.testBit_zero]; cases e <;> simp
  have h3 : (⟨(col j e).val / 2, (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).2
      (lt_of_lt_of_eq (col j e).isLt (Nat.mul_comm 2 h))⟩ : Fin h) = j := Fin.ext h1
  show (b x ⟨(col j e).val / 2, _⟩ == (col j e).val.testBit 0) = (b x j == e)
  rw [h3]
  show (b x j == (2 * j.val + e.toNat).testBit 0) = (b x j == e)
  rw [h2]

theorem col_inj {h : ℕ} {j j' : Fin h} {e e' : Bool} (hc : col j e = col j' e') : j = j' ∧ e = e' := by
  have hv : 2 * j.val + e.toNat = 2 * j'.val + e'.toNat := congrArg Fin.val hc
  constructor
  · apply Fin.ext
    rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> omega
  · rcases e with _ | _ <;> rcases e' with _ | _ <;>
      simp only [Bool.toNat_false, Bool.toNat_true] at hv <;> first | rfl | (exfalso; omega)

theorem lit_sep {r h : ℕ} (b : Fin r → Fin h → Bool) (hb : Function.Injective b) (u v : Fin r)
    (huv : u ≠ v) : ∃ c, lit b u c = true ∧ lit b v c = false := by
  have hne : b u ≠ b v := fun e => huv (hb e)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  refine ⟨col j (b u j), ?_, ?_⟩
  · rw [lit_col]; simp
  · rw [lit_col]; revert hj; cases b u j <;> cases b v j <;> simp

theorem forcedL_card {r h : ℕ} (b : Fin r → Fin h → Bool) (hb : Function.Injective b) (hr : 2 ≤ r) :
    (RepReads.forcedL (lit b)).card = r := by
  have hall : RepReads.forcedL (lit b) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun u => ?_
    obtain ⟨v, hv⟩ : ∃ v : Fin r, u ≠ v := by
      by_cases h0 : u.val = 0
      · exact ⟨⟨1, by omega⟩, fun e => by have : u.val = 1 := congrArg Fin.val e; omega⟩
      · exact ⟨⟨0, by omega⟩, fun e => by have : u.val = 0 := congrArg Fin.val e; omega⟩
    obtain ⟨c, h1, h2⟩ := lit_sep b hb u v hv
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, c, h1, v, h2⟩
  rw [hall]; simp

theorem col_forced {r h : ℕ} (b : Fin r → Fin h → Bool) (u : Fin r) (j : Fin h) :
    col j (b u j) ∈ RepReads.forcedR (lit b) := by
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, u, ?_, col j (!b u j), ?_⟩
  · rw [lit_col]; simp
  · rw [lit_col]; cases b u j <;> rfl

theorem forcedR_card {r h : ℕ} (b : Fin r → Fin h → Bool)
    (hnc : ∀ i, ∃ u v, b u i = false ∧ b v i = true) : (RepReads.forcedR (lit b)).card = 2 * h := by
  have hall : RepReads.forcedR (lit b) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun c => ?_
    have hjlt : c.val / 2 < h := by have := c.isLt; omega
    obtain ⟨j, hj⟩ : ∃ j : Fin h, j.val = c.val / 2 := ⟨⟨c.val / 2, hjlt⟩, rfl⟩
    obtain ⟨u, v, hu, hv⟩ := hnc j
    have hbit := Nat.testBit_zero c.val
    by_cases hodd : c.val % 2 = 1
    · have hc : c = col j true := by
        apply Fin.ext; show c.val = 2 * j.val + 1; omega
      have hf := col_forced b v j
      rw [hv] at hf; rw [hc]; exact hf
    · have hc : c = col j false := by
        apply Fin.ext; show c.val = 2 * j.val + 0; omega
      have hf := col_forced b u j
      rw [hu] at hf; rw [hc]; exact hf
  rw [hall]; simp

theorem two_rows {h t : ℕ} (b : Fin 2 → Fin h → Bool) (hb : Function.Injective b) (hh : 2 ≤ h)
    (hrep : RepSizeAtMost (lit b) t) : 4 ≤ t := by
  have h1 := RepReads.reads_le (lit b) hrep
  have h2 := forcedL_card b hb le_rfl
  have hne : b 0 ≠ b 1 := fun e => by have := hb e; simp at this
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  obtain ⟨j', hj'⟩ : ∃ j' : Fin h, j' ≠ j := by
    by_cases h0 : j.val = 0
    · exact ⟨⟨1, by omega⟩, fun e => by have : (1 : ℕ) = j.val := congrArg Fin.val e; omega⟩
    · exact ⟨⟨0, by omega⟩, fun e => by have : (0 : ℕ) = j.val := congrArg Fin.val e; omega⟩
  have h3 : 2 < (RepReads.forcedR (lit b)).card := by
    rw [Finset.two_lt_card_iff]
    refine ⟨col j (b 0 j), col j (b 1 j), col j' (b 0 j'), col_forced b 0 j, col_forced b 1 j,
      col_forced b 0 j', ?_, ?_, ?_⟩
    · intro e; exact hj (col_inj e).2
    · intro e; exact hj' (col_inj e).1.symm
    · intro e; exact hj' (col_inj e).1.symm
  omega

theorem path_bound {r h s : ℕ} (b : Fin r → Fin h → Bool) (hb : Function.Injective b) (hr : 3 ≤ r)
    (hh : 1 ≤ h) (hnc : ∀ i, ∃ u v, b u i = false ∧ b v i = true) (hrep : RepSizeAtMost (lit b) s) :
    r + 2 * h ≤ s := by
  have hL := forcedL_card b hb (by omega)
  have hR := forcedR_card b hnc
  obtain ⟨j1, -⟩ : ∃ j1 : Fin h, j1.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨u, x, hux, hag⟩ : ∃ u x : Fin r, u ≠ x ∧ b u j1 = b x j1 := by
    obtain ⟨a0, ha0⟩ : ∃ a : Fin r, a.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨a1, ha1⟩ : ∃ a : Fin r, a.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
    obtain ⟨a2, ha2⟩ : ∃ a : Fin r, a.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
    have h01 : a0 ≠ a1 := fun e => by have := congrArg Fin.val e; omega
    have h02 : a0 ≠ a2 := fun e => by have := congrArg Fin.val e; omega
    have h12 : a1 ≠ a2 := fun e => by have := congrArg Fin.val e; omega
    by_cases e01 : b a0 j1 = b a1 j1
    · exact ⟨a0, a1, h01, e01⟩
    · by_cases e02 : b a0 j1 = b a2 j1
      · exact ⟨a0, a2, h02, e02⟩
      · refine ⟨a1, a2, h12, ?_⟩
        revert e01 e02
        cases b a0 j1 <;> cases b a1 j1 <;> cases b a2 j1 <;> simp
  obtain ⟨j2, hj2⟩ := Function.ne_iff.1 (fun e : b u = b x => hux (hb e))
  obtain ⟨u0, v0, hu0, hv0⟩ := hnc j1
  have huv : lit b u (col j1 (b u j1)) = true := by rw [lit_col]; simp
  have huw : lit b u (col j2 (b u j2)) = true := by rw [lit_col]; simp
  have hxv : lit b x (col j1 (b u j1)) = true := by rw [lit_col, hag]; simp
  have hxw : lit b x (col j2 (b u j2)) = false := by
    rw [lit_col]; revert hj2; cases b u j2 <;> cases b x j2 <;> simp
  have hw' : ∃ w', lit b u w' = false := ⟨col j1 (!b u j1), by rw [lit_col]; cases b u j1 <;> rfl⟩
  have hu' : ∃ u', lit b u' (col j1 (b u j1)) = false := by
    rcases hbu : b u j1 with _ | _
    · exact ⟨v0, by rw [lit_col, hv0]; rfl⟩
    · exact ⟨u0, by rw [lit_col, hu0]; rfl⟩
  have hp := RepPath.path r (2 * h) s (lit b) u x _ _ huv huw hxv hxw hw' hu' hrep
  change (RepReads.forcedL (lit b)).card + (RepReads.forcedR (lit b)).card ≤ s at hp
  omega

theorem bit_inj {k m : ℕ} (name : Fin m → Fin (2 ^ k)) (hinj : Function.Injective name) :
    Function.Injective (fun (a : Fin m) (j : Fin k) => (name a).val.testBit j.val) := by
  intro a a' e
  apply hinj
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun e ⟨i, hi⟩
  · have hp : ∀ x : Fin (2 ^ k), x.val.testBit i = false := fun x =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hp, hp]

abbrev Mem (k m s : ℕ) (name : Fin m → Fin (2 ^ k)) (r h : ℕ) : Prop :=
  ∃ (row : Fin r → Fin m) (coord : Fin h → Fin k) (t : ℕ),
    Function.Injective row ∧ Function.Injective coord ∧
    Function.Injective (fun (a' : Fin r) (j' : Fin h) => (name (row a')).val.testBit (coord j').val) ∧
    RepSizeAtMost (lit fun (a' : Fin r) (j' : Fin h) => (name (row a')).val.testBit (coord j').val) t ∧
    t + 2 * (m - r) ≤ s

theorem mem_two {k m s : ℕ} (name : Fin m → Fin (2 ^ k)) (hm : 2 ≤ m) (hs : s < 2 * m) {h : ℕ}
    (hh : 2 ≤ h) (hM : Mem k m s name 2 h) : False := by
  obtain ⟨row, coord, t, _, _, hb, hrep, hbud⟩ := hM
  have := two_rows _ hb hh hrep
  omega

theorem mem_drop {k m s : ℕ} (name : Fin m → Fin (2 ^ k)) {r h : ℕ} (row : Fin r → Fin m)
    (coord : Fin (h + 1) → Fin k) (t : ℕ) (hrow : Function.Injective row)
    (hcoord : Function.Injective coord)
    (hb : Function.Injective
      (fun (a' : Fin r) (j' : Fin (h + 1)) => (name (row a')).val.testBit (coord j').val))
    (hrep : RepSizeAtMost
      (lit fun (a' : Fin r) (j' : Fin (h + 1)) => (name (row a')).val.testBit (coord j').val) t)
    (hbud : t + 2 * (m - r) ≤ s) (i : Fin (h + 1))
    (hconst : ∀ u v : Fin r,
      (name (row u)).val.testBit (coord i).val = (name (row v)).val.testBit (coord i).val) :
    Mem k m s name r h := by
  refine ⟨row, coord ∘ i.succAbove, t, hrow, hcoord.comp Fin.succAbove_right_injective, ?_, ?_, hbud⟩
  · intro a1 a2 e
    apply hb
    funext j
    by_cases hji : j = i
    · subst hji; exact hconst a1 a2
    · obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hji
      exact congrFun e z
  · have hlt : ∀ c : Fin (2 * h), c.val / 2 < h := fun c => by have := c.isLt; omega
    let f : Fin (2 * h) → Fin (2 * (h + 1)) :=
      fun c => col (i.succAbove ⟨c.val / 2, hlt c⟩) (c.val.testBit 0)
    have hf : Function.Injective f := by
      intro c c' e
      obtain ⟨e1, e2⟩ := col_inj e
      have e3 : c.val / 2 = c'.val / 2 := congrArg Fin.val (Fin.succAbove_right_injective e1)
      rw [Nat.testBit_zero, Nat.testBit_zero] at e2
      have e4 := decide_eq_decide.1 e2
      apply Fin.ext
      omega
    have hsub := PEqualNP.Outside.L_lib_370 r (2 * (h + 1)) r (2 * h) t _ id f
      Function.injective_id hf hrep
    have heq : (fun (u : Fin r) (v : Fin (2 * h)) =>
        lit (fun (a' : Fin r) (j' : Fin (h + 1)) => (name (row a')).val.testBit (coord j').val)
          (id u) (f v))
        = lit (fun (a' : Fin r) (j' : Fin h) =>
          (name (row a')).val.testBit ((coord ∘ i.succAbove) j').val) := by
      funext u v
      show lit _ u (col _ _) = _
      rw [lit_col]; rfl
    rw [← heq]; exact hsub

theorem core (k m s : ℕ) (name : Fin m → Fin (2 ^ k)) (hk : 2 ≤ k) (hm : 2 ≤ m)
    (hinj : Function.Injective name)
    (hrep : RepSizeAtMost (lit fun (a : Fin m) (j : Fin k) => (name a).val.testBit j.val) s)
    (hs : s < 2 * m) :
    ∃ (r h : ℕ) (row : Fin r → Fin m) (coord : Fin h → Fin k) (D : Circuit),
      Function.Injective row ∧ Function.Injective coord ∧
      Function.Injective (fun (a' : Fin r) (j' : Fin h) => (name (row a')).val.testBit (coord j').val) ∧
      2 ≤ h ∧ 2 * h < r ∧
      (∀ i, ∃ u v, (name (row u)).val.testBit (coord i).val = false ∧
        (name (row v)).val.testBit (coord i).val = true) ∧
      Monotone2 D ∧ NestedCover.ReadsBack (r + 2 * h) D ∧
      Represents (lit fun (a' : Fin r) (j' : Fin h) => (name (row a')).val.testBit (coord j').val) D ∧
      D.size + 2 * (m - r) ≤ s ∧ D.size < 2 * r ∧
      ∀ u : Fin r, NestedCover.readsIn D (Finset.range D.size) u.val = 1 ∧
        ∃ (j : Fin D.gates.length) (w : ℕ), (D.gates.get j).op = GateOp.or ∧
          ((D.gates.get j).inputs = [u.val, w] ∨ (D.gates.get j).inputs = [w, u.val]) := by
  classical
  have hinit : Mem k m s name m k :=
    ⟨id, id, s, Function.injective_id, Function.injective_id, bit_inj name hinj, hrep, by simp⟩
  by_cases hm3 : 3 ≤ m
  swap
  · have h2 : m = 2 := by omega
    subst h2
    exact (mem_two name hm hs hk hinit).elim
  have hex : ∃ N r h, r + h = N ∧ 3 ≤ r ∧ Mem k m s name r h := ⟨m + k, m, k, rfl, hm3, hinit⟩
  obtain ⟨r, h, hN, hr3, hM⟩ := Nat.find_spec hex
  have hmin : ∀ r' h', r' + h' < r + h → 3 ≤ r' → Mem k m s name r' h' → False := by
    intro r' h' hlt h3' hM'
    exact Nat.find_min hex (by omega) ⟨r', h', rfl, h3', hM'⟩
  obtain ⟨row, coord, t, hrow, hcoord, hb, hrepb, hbud⟩ := hM
  have hrm : r ≤ m := by simpa using Fintype.card_le_of_injective row hrow
  have hh2 : 2 ≤ h := by
    have hc := Fintype.card_le_of_injective _ hb
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hc
    by_contra hlt
    have h21 : 2 ^ h ≤ 2 := by
      calc 2 ^ h ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    omega
  have hnc : ∀ i : Fin h, ∃ u v : Fin r, (name (row u)).val.testBit (coord i).val = false ∧
      (name (row v)).val.testBit (coord i).val = true := by
    intro i
    by_contra hcon
    have hconst : ∀ u v : Fin r,
        (name (row u)).val.testBit (coord i).val = (name (row v)).val.testBit (coord i).val := by
      intro u v
      by_contra hne
      apply hcon
      rcases hu : (name (row u)).val.testBit (coord i).val with _ | _
      · rcases hv : (name (row v)).val.testBit (coord i).val with _ | _
        · exact absurd (hu.trans hv.symm) hne
        · exact ⟨u, v, hu, hv⟩
      · rcases hv : (name (row v)).val.testBit (coord i).val with _ | _
        · exact ⟨v, u, hv, hu⟩
        · exact absurd (hu.trans hv.symm) hne
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    exact hmin r h' (by omega) hr3 (mem_drop name row coord t hrow hcoord hb hrepb hbud i hconst)
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rcases PEqualNP.Outside.L_meta_25491 n (2 * h) t
      (lit fun (a' : Fin (n + 1)) (j' : Fin h) => (name (row a')).val.testBit (coord j').val)
      (by omega) (fun u v huv => lit_sep _ hb u v huv) hrepb with
    ⟨u, t', ht', hrep'⟩ | ⟨C, hCm, hCs, hCb, hCr, hCu⟩
  · exfalso
    have hM' : Mem k m s name n h :=
      ⟨row ∘ u.succAbove, coord, t', hrow.comp Fin.succAbove_right_injective, hcoord,
        fun a1 a2 e => Fin.succAbove_right_injective (hb e), hrep', by omega⟩
    by_cases hn2 : n = 2
    · subst hn2; exact mem_two name hm hs hh2 hM'
    · exact hmin n h (by omega) (by omega) hM'
  · have hpb := path_bound _ hb (by omega) (by omega) hnc ⟨C, hCm, le_rfl, hCr⟩
    exact ⟨n + 1, h, row, coord, C, hrow, hcoord, hb, hh2, by omega, hnc, hCm, hCb, hCr, by omega,
      by omega, hCu⟩

end PEqualNP.Outside.L_meta_25500_aux

theorem PEqualNP.Outside.L_meta_25500 : (∀ (k m s : ℕ) (name : Fin m → Fin (2 ^ k)),
  let bit := fun (a : Fin m) (j : Fin k) => (name a).val.testBit j.val
  let literals {r h : ℕ} (b : Fin r → Fin h → Bool)
      (x : Fin r) (c : Fin (2 * h)) :=
    b x ⟨c.val / 2, (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).2
      (lt_of_lt_of_eq c.isLt (Nat.mul_comm 2 h))⟩ == c.val.testBit 0
  2 ≤ k → 2 ≤ m → Function.Injective name →
  PEqualNP.Represents.RepSizeAtMost (literals bit) s → s < 2 * m →
  ∃ (r h : ℕ) (row : Fin r → Fin m) (coord : Fin h → Fin k)
      (D : PEqualNP.CircuitLowerBounds.Circuit),
    let b := fun a' j' => bit (row a') (coord j')
    Function.Injective row ∧ Function.Injective coord ∧ Function.Injective b ∧
    2 ≤ h ∧ 2 * h < r ∧
    (∀ i, ∃ u v, b u i = false ∧ b v i = true) ∧
    PEqualNP.MetaComplexity.Monotone2 D ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + 2 * h) D ∧
    PEqualNP.Represents.Represents (literals b) D ∧
    D.size + 2 * (m - r) ≤ s ∧ D.size < 2 * r ∧
    ∀ u : Fin r,
      PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) u.val = 1 ∧
      ∃ (j : Fin D.gates.length) (w : ℕ),
        (D.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ((D.gates.get j).inputs = [u.val, w] ∨ (D.gates.get j).inputs = [w, u.val])) :=
  fun k m s name => PEqualNP.Outside.L_meta_25500_aux.core k m s name
