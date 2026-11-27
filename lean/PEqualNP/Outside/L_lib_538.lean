import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_538_aux

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

def signZ (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma signZ_add (a b : ZMod 2) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma signZ_sum {ι : Type*} (t : Finset ι) (f : ι → ZMod 2) :
    signZ (∑ i ∈ t, f i) = ∏ i ∈ t, signZ (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, signZ_add, ih]

lemma single_pair_walsh (c p q : ZMod 2) :
    (∑ a : ZMod 2, ∑ b : ZMod 2, signZ (c * (a * b) + p * a + q * b)) =
      if c = 0 then (if p = 0 ∧ q = 0 then 4 else 0) else 2 * signZ (p * q) := by
  fin_cases c <;> fin_cases p <;> fin_cases q <;> decide

end PEqualNP.Outside.L_lib_538_aux

theorem PEqualNP.Outside.L_lib_538 :
∀ s : ℕ,
  let V := Fin s → ZMod 2
  let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
  let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
  ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
  (∀ x y i, Z x y i =
    (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
    (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
  ∀ p q : V,
    let c := fun (j : Fin s) =>
      γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
    (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
      ∏ j : Fin s,
        if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
        else 2 * sign (p j * q j) := by
  intro s V dot sign A B γ Z hZ p q c
  let phi : V × V → V × V := fun uv =>
    (fun i => uv.1 i + ∑ j ∈ Finset.Iio i, A i j * (uv.1 j * uv.2 j),
     fun i => uv.2 i + ∑ j ∈ Finset.Iio i, B i j * (uv.1 j * uv.2 j))
  let psi : V × V → V × V := fun xy =>
    (fun i => xy.1 i + ∑ j ∈ Finset.Iio i, A i j * Z xy.1 xy.2 j,
     fun i => xy.2 i + ∑ j ∈ Finset.Iio i, B i j * Z xy.1 xy.2 j)
  have hZ_phi : ∀ (u v : V) (i : Fin s), Z (phi (u, v)).1 (phi (u, v)).2 i = u i * v i := by
    intro u v i
    have hstrong : ∀ (m : ℕ) (hm : m < s),
        Z (phi (u, v)).1 (phi (u, v)).2 ⟨m, hm⟩ = u ⟨m, hm⟩ * v ⟨m, hm⟩ := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro hm
        rw [hZ]
        have hsumA : ∑ j ∈ Finset.Iio (⟨m, hm⟩ : Fin s), A ⟨m, hm⟩ j * Z (phi (u, v)).1 (phi (u, v)).2 j =
            ∑ j ∈ Finset.Iio (⟨m, hm⟩ : Fin s), A ⟨m, hm⟩ j * (u j * v j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hlt : j.val < m := Fin.lt_def.mp (Finset.mem_Iio.mp hj)
          rw [ih j.val hlt j.isLt]
        have hsumB : ∑ j ∈ Finset.Iio (⟨m, hm⟩ : Fin s), B ⟨m, hm⟩ j * Z (phi (u, v)).1 (phi (u, v)).2 j =
            ∑ j ∈ Finset.Iio (⟨m, hm⟩ : Fin s), B ⟨m, hm⟩ j * (u j * v j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hlt : j.val < m := Fin.lt_def.mp (Finset.mem_Iio.mp hj)
          rw [ih j.val hlt j.isLt]
        rw [hsumA, hsumB]
        dsimp only [phi]
        rw [add_assoc, PEqualNP.Outside.L_lib_538_aux.zmod2_add_self, add_zero]
        rw [add_assoc, PEqualNP.Outside.L_lib_538_aux.zmod2_add_self, add_zero]
    exact hstrong i.val i.isLt
  let ePhi : (V × V) ≃ (V × V) :=
    { toFun := phi,
      invFun := psi,
      left_inv := fun ⟨u, v⟩ => by
        ext i
        · dsimp only [psi]
          simp_rw [hZ_phi u v]
          dsimp only [phi]
          rw [add_assoc, PEqualNP.Outside.L_lib_538_aux.zmod2_add_self, add_zero]
        · dsimp only [psi]
          simp_rw [hZ_phi u v]
          dsimp only [phi]
          rw [add_assoc, PEqualNP.Outside.L_lib_538_aux.zmod2_add_self, add_zero],
      right_inv := fun ⟨x, y⟩ => by
        ext i
        · dsimp only [phi, psi]
          have hmul : ∀ j : Fin s,
              (x j + ∑ k ∈ Finset.Iio j, A j k * Z x y k) *
              (y j + ∑ k ∈ Finset.Iio j, B j k * Z x y k) = Z x y j := fun j => (hZ x y j).symm
          simp_rw [hmul]
          rw [add_assoc, PEqualNP.Outside.L_lib_538_aux.zmod2_add_self, add_zero]
        · dsimp only [phi, psi]
          have hmul : ∀ j : Fin s,
              (x j + ∑ k ∈ Finset.Iio j, A j k * Z x y k) *
              (y j + ∑ k ∈ Finset.Iio j, B j k * Z x y k) = Z x y j := fun j => (hZ x y j).symm
          simp_rw [hmul]
          rw [add_assoc, PEqualNP.Outside.L_lib_538_aux.zmod2_add_self, add_zero] }
  have hsum_pair : (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
      ∑ uv : V × V, sign (dot γ (Z (phi uv).1 (phi uv).2) + dot p (phi uv).1 + dot q (phi uv).2) := by
    rw [← Fintype.sum_prod_type']
    exact (Equiv.sum_comp ePhi (fun xy : V × V => sign (dot γ (Z xy.1 xy.2) + dot p xy.1 + dot q xy.2))).symm
  rw [hsum_pair]
  have hexp : ∀ uv : V × V,
      dot γ (Z (phi uv).1 (phi uv).2) + dot p (phi uv).1 + dot q (phi uv).2 =
      ∑ j : Fin s, (c j * (uv.1 j * uv.2 j) + p j * uv.1 j + q j * uv.2 j) := by
    rintro ⟨u, v⟩
    dsimp only [dot]
    simp_rw [hZ_phi u v]
    dsimp only [phi]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hswapA : (∑ i : Fin s, p i * ∑ j ∈ Finset.Iio i, A i j * (u j * v j)) =
        ∑ j : Fin s, (∑ i ∈ Finset.Ioi j, p i * A i j) * (u j * v j) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      have h1 : ∀ i : Fin s, (∑ j ∈ Finset.Iio i, p i * (A i j * (u j * v j))) =
          ∑ j : Fin s, if j < i then p i * A i j * (u j * v j) else 0 := by
        intro i
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun j : Fin s => j < i) = Finset.Iio i := by
          ext j; simp
        rw [hf]
        apply Finset.sum_congr rfl; intro j _; ring
      have h2 : ∀ j : Fin s, (∑ i ∈ Finset.Ioi j, p i * A i j * (u j * v j)) =
          ∑ i : Fin s, if j < i then p i * A i j * (u j * v j) else 0 := by
        intro j
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun i : Fin s => j < i) = Finset.Ioi j := by
          ext i; simp
        rw [hf]
      simp_rw [h1, h2]
      exact Finset.sum_comm
    have hswapB : (∑ i : Fin s, q i * ∑ j ∈ Finset.Iio i, B i j * (u j * v j)) =
        ∑ j : Fin s, (∑ i ∈ Finset.Ioi j, q i * B i j) * (u j * v j) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      have h1 : ∀ i : Fin s, (∑ j ∈ Finset.Iio i, q i * (B i j * (u j * v j))) =
          ∑ j : Fin s, if j < i then q i * B i j * (u j * v j) else 0 := by
        intro i
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun j : Fin s => j < i) = Finset.Iio i := by
          ext j; simp
        rw [hf]
        apply Finset.sum_congr rfl; intro j _; ring
      have h2 : ∀ j : Fin s, (∑ i ∈ Finset.Ioi j, q i * B i j * (u j * v j)) =
          ∑ i : Fin s, if j < i then q i * B i j * (u j * v j) else 0 := by
        intro j
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun i : Fin s => j < i) = Finset.Ioi j := by
          ext i; simp
        rw [hf]
      simp_rw [h1, h2]
      exact Finset.sum_comm
    rw [hswapA, hswapB]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [c]
    rw [Finset.sum_add_distrib]
    ring
  simp_rw [hexp]
  have hsign_eq : ∀ uv : V × V,
      sign (∑ j : Fin s, (c j * (uv.1 j * uv.2 j) + p j * uv.1 j + q j * uv.2 j)) =
      ∏ j : Fin s, PEqualNP.Outside.L_lib_538_aux.signZ (c j * (uv.1 j * uv.2 j) + p j * uv.1 j + q j * uv.2 j) :=
    fun uv => PEqualNP.Outside.L_lib_538_aux.signZ_sum Finset.univ _
  simp_rw [hsign_eq]
  let eProd : (Fin s → ZMod 2 × ZMod 2) ≃ (V × V) :=
    { toFun := fun f => (fun j => (f j).1, fun j => (f j).2),
      invFun := fun uv j => (uv.1 j, uv.2 j),
      left_inv := fun f => by ext j <;> rfl,
      right_inv := fun ⟨u, v⟩ => by ext j <;> rfl }
  rw [← Equiv.sum_comp eProd]
  dsimp only [eProd, Equiv.coe_fn_mk]
  rw [← Fintype.prod_sum (fun j (ab : ZMod 2 × ZMod 2) =>
    PEqualNP.Outside.L_lib_538_aux.signZ (c j * (ab.1 * ab.2) + p j * ab.1 + q j * ab.2))]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fintype.sum_prod_type]
  exact PEqualNP.Outside.L_lib_538_aux.single_pair_walsh (c j) (p j) (q j)
