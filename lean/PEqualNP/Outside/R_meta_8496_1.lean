import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_8496_1
    (geometric : ∀ C : Circuit,
      let m := fun (j : ℕ) (v : Fin 14) =>
        (gateAt C j).op=.and ∧ gateVal 14 C j (pairInput 0 7)=true ∧
        ∀ r : Fin 2,wireVal 14 C (opnd C j r) (pairInput v v)=false
      C.size≤27 → IsAO2 14 C → (∀ j<C.size,(gateAt C j).inputs.Nodup) → (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
       ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) →
      ∀ i j, m i 0 → m j 7 → 9≤((Finset.univ : Finset (Fin 14)).val.filter (fun t =>
        (List.range (14+C.size)).any (fun w=>decide (2≤(PEqualNP.TopForm.readers 0 C w).card) &&
          wireVal 14 C w (fun v=>decide (v=t)))=true)).card)
    (remaining : ∀ C : Circuit,
      let m := fun (j : ℕ) (v : Fin 14) =>
        (gateAt C j).op=.and ∧ gateVal 14 C j (pairInput 0 7)=true ∧
        ∀ r : Fin 2,wireVal 14 C (opnd C j r) (pairInput v v)=false
      C.size≤27 → IsAO2 14 C → (∀ j<C.size,(gateAt C j).inputs.Nodup) → (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
       ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) → 9≤((Finset.univ : Finset (Fin 14)).val.filter (fun t =>
        (List.range (14+C.size)).any (fun w=>decide (2≤(PEqualNP.TopForm.readers 0 C w).card) &&
          wireVal 14 C w (fun v=>decide (v=t)))=true)).card →
      29≤(C.gates.foldl (fun (ns : List ℕ) (g : Gate)=>ns++[(g.inputs.map (fun w=>ns.getD w 0)).sum])
         (List.replicate 14 1)).getD C.output 0 →
      ∀ i j, InCone 14 C i j → m i 0 → m j 7 → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List ℕ := [(16771220242439 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (182572334459126281 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)];   have x3 : ℕ → Fin (14 : ℕ) → Prop := fun (x3 : ℕ) (x4 : Fin (14 : ℕ)) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x5 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x5) (PEqualNP.EdgeOwnership.pairInput x4 x4) = Bool.false;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (29 : ℕ) ≤ (List.foldl (fun (x7 : List ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => x7 ++ [(List.map (fun (x9 : ℕ) => x7.getD x9 (0 : ℕ)) x8.inputs).sum]) (List.replicate (14 : ℕ) (1 : ℕ)) x1.gates).getD x1.output (0 : ℕ) → (∀ (x8 : Fin (58 : ℕ)), x1.eval (List.ofFn fun (x9 : Fin (14 : ℕ)) => (x2.getD ↑x9 (0 : ℕ)).testBit ↑x8) = Decidable.decide (↑x8 < (21 : ℕ))) → ∀ (x9 x10 : ℕ), PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x9 x10 → (14 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x10 (x1.output - (14 : ℕ)) → x3 x9 (0 : Fin (14 : ℕ)) → x3 x10 (7 : Fin (14 : ℕ)) → False) := by
  intro C
  dsimp only
  intro small ao distinct unfolded pass i j nested _ lower upper
  let gateBit (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  let stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

  let WiresLE (w z : List Bool) : Prop :=
    w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

  let IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

  have monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
      IsMonoGate g := by
    simpa [IsMonoGate] using (hC g hg).1

  have bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
      (hw : gateBit w g = true) : gateBit z g = true := by
    rcases hg with hop | hop
    · simp only [gateBit,hop] at hw ⊢
      change (g.inputs.map (fun i=>w.getD i false)).all id=true at hw
      change (g.inputs.map (fun i=>z.getD i false)).all id=true
      simp only [List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at hw ⊢
      exact fun i hi => h.2 i (hw i hi)
    · simp only [gateBit,hop] at hw ⊢
      change (g.inputs.map (fun i=>w.getD i false)).any id=true at hw
      change (g.inputs.map (fun i=>z.getD i false)).any id=true
      simp only [List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq] at hw ⊢
      obtain ⟨i, hi, hv⟩ := hw
      exact ⟨i, hi, h.2 i hv⟩

  have append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
      (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
    refine ⟨by simp [h.1], ?_⟩
    intro i hi
    rw [List.getD_eq_getElem?_getD] at hi ⊢
    by_cases hlt : i < w.length
    · rw [List.getElem?_append_left hlt] at hi
      rw [List.getElem?_append_left (by rwa [← h.1])]
      simpa only [List.getD_eq_getElem?_getD] using h.2 i
        (by simpa only [List.getD_eq_getElem?_getD] using hi)
    · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
      rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
      cases hd : i - w.length with
      | zero =>
        simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
        exact hab hi
      | succ k => simp [hd] at hi

  have fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
      {w z : List Bool} (h : WiresLE w z) :
      WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
    induction gs generalizing w z with
    | nil => exact h
    | cons g gs ih =>
      exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
        (append_mono h (bit_mono h (hg g (by simp))))

  have ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
      (List.ofFn x).getD u.val false = x u := by
    simp [List.getD_eq_getElem?_getD]

  have ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
      WiresLE (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hlt : i < n
    · rw [ofFn_getD y ⟨i, hlt⟩]
      exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
      cases hi

  let f := fun x : Fin 14 → Bool => C.eval (List.ofFn x)
  have hm : Monotone f := by
    intro x y hxy
    apply Bool.le_iff_imp.mpr
    exact (fold_mono C.gates (fun g hg=>ao.1 g hg) (ofFn_mono (fun v=>Bool.le_iff_imp.mp (hxy v)))).2 C.output
  let tbl : List ℕ := [(16771220242439 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (182572334459126281 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]
  let col := fun (r : ℕ) (v : Fin 14) => (tbl.getD v.val 0).testBit r
  have hv : ∀ k : Fin 58,f (fun v=>col k.val v)=decide (k.val<21) := pass
  have T2 : ∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) →
      ∃ k : Fin 58, k.val < 21 ∧ ∀ i : Fin 14, col k.val i = true →
        (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) := by
    dsimp only [col,tbl]
    decide +kernel

  have T3 : ∀ m : Fin 128, ∃ k : Fin 58, 21 ≤ k.val ∧
      (∀ l : Fin 7, m.val.testBit l.val = true → col k.val (Fin.natAdd 7 l) = true) ∧
      (∀ p : Fin 7, (∀ l : Fin 7, m.val.testBit l.val = true → ¬ (p = l ∨ p = l + 1 ∨ p = l + 3)) →
        col k.val (Fin.castAdd 7 p) = true) := by
    dsimp only [col,tbl]
    decide +kernel
  have full : (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
       ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) := by
    intro x
    change f x = true ↔ _
    constructor
    · intro hx
      by_contra hno
      have hm7 : Nat.ofBits (fun l : Fin 7 => x (Fin.natAdd 7 l)) < 128 :=
        Nat.ofBits_lt_two_pow _
      obtain ⟨k, hk21, hL, hP⟩ := T3 ⟨_, hm7⟩
      have hbit : ∀ l : Fin 7, (Nat.ofBits (fun l : Fin 7 => x (Fin.natAdd 7 l))).testBit l.val
          = x (Fin.natAdd 7 l) := fun l => Nat.testBit_ofBits_lt _ _ l.isLt
      have hle : x ≤ (fun i : Fin 14 => col k.val i) := by
        intro i
        refine Fin.addCases (m := 7) (n := 7) (motive := fun i => x i ≤ col k.val i) ?_ ?_ i
        · intro p
          rw [Bool.le_iff_imp]
          intro hp
          apply hP p
          intro l hl hinc
          exact hno ⟨p, l, hinc, hp, (hbit l) ▸ hl⟩
        · intro l
          rw [Bool.le_iff_imp]
          intro hl
          apply hL l
          show (Nat.ofBits (fun l : Fin 7 => x (Fin.natAdd 7 l))).testBit l.val = true
          rw [hbit l]
          exact hl
      have h1 := hm hle
      rw [hx, hv k, decide_eq_false (by omega)] at h1
      exact absurd h1 (by decide)
    · rintro ⟨p, l, hinc, hp, hl⟩
      obtain ⟨k, hk, hsub⟩ := T2 p l hinc
      have hle : (fun i : Fin 14 => col k.val i) ≤ x := by
        intro i
        rw [Bool.le_iff_imp]
        intro hi
        rcases hsub i hi with rfl | rfl
        · exact hp
        · exact hl
      have h1 := hm hle
      rw [hv k, decide_eq_true hk] at h1
      exact Bool.eq_true_of_true_le h1
  exact remaining C small ao distinct full (geometric C small ao distinct full i j lower upper)
    unfolded i j nested lower upper
