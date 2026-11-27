import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18769_2
    (hElimDummy0 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        C.eval (List.ofFn fun (_ : Fin (26 : ℕ)) => Bool.false) = Bool.false →
        C.eval (List.ofFn (Fin.cons Bool.false fun (_ : Fin (25 : ℕ)) => Bool.true)) = Bool.true →
        ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsAO2 (25 : ℕ) C' ∧
          C'.size ≤ C.size ∧
          ∀ (f : Fin (25 : ℕ) → Bool), C'.eval (List.ofFn f) = C.eval (List.ofFn (Fin.cons Bool.false f)))
    (hPure25LB :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (25 : ℕ) C →
        (∀ (f : Fin (25 : ℕ) → Bool), C.eval (List.ofFn f) = Bool.true ↔
          ∃ (a : Fin (12 : ℕ)) (b : Fin (13 : ℕ)),
            (a.succ = b ∨ a.succ = b + (1 : Fin (13 : ℕ)) ∨ a.succ = b + (3 : Fin (13 : ℕ)) ∨ a.succ = b + (9 : Fin (13 : ℕ))) ∧
            f (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ f (Fin.natAdd (12 : ℕ) b) = Bool.true) →
        (59 : ℕ) ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (59 : ℕ) ≤ x1.size) := by
  intro C _ hAO hFun _
  have hCast : ∀ (a : Fin (12 : ℕ)), Fin.castAdd (13 : ℕ) a.succ = (Fin.castAdd (13 : ℕ) a).succ :=
    fun _ => Fin.ext rfl
  have hNat : ∀ (b : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) b = (Fin.natAdd (12 : ℕ) b).succ :=
    fun b => Fin.ext (by show (13 : ℕ) + b.val = ((12 : ℕ) + b.val) + (1 : ℕ); omega)
  have hFalse : C.eval (List.ofFn fun (_ : Fin (26 : ℕ)) => Bool.false) = Bool.false :=
    Bool.eq_false_iff.mpr fun ht =>
      Exists.elim ((hFun _).mp ht) fun _ h1 =>
        Exists.elim h1 fun _ h2 => Bool.false_ne_true h2.2.2.1
  have hTrue : C.eval (List.ofFn (Fin.cons Bool.false fun (_ : Fin (25 : ℕ)) => Bool.true)) = Bool.true :=
    (hFun _).mpr ⟨(1 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), Or.inl rfl, by decide, rfl, rfl⟩
  exact Exists.elim (hElimDummy0 C hAO hFalse hTrue) fun C' hC' =>
    Nat.le_trans
      (hPure25LB C' hC'.1 fun f =>
        Iff.intro
          (fun ht =>
            Exists.elim ((hFun (Fin.cons Bool.false f)).mp (Eq.trans (hC'.2.2 f).symm ht)) fun x5 h1 =>
              Exists.elim h1 fun x6 h2 => by
                have hne : x5 ≠ (0 : Fin (13 : ℕ)) := h2.2.1
                have ha : (x5.pred hne).succ = x5 := Fin.succ_pred x5 hne
                have hRel := h2.1
                have hx5 := h2.2.2.1
                have hx6 := h2.2.2.2
                rw [← ha] at hRel hx5
                rw [hCast (x5.pred hne), Fin.cons_succ] at hx5
                rw [hNat x6, Fin.cons_succ] at hx6
                exact ⟨x5.pred hne, x6, hRel, hx5, hx6⟩)
          (fun hEx =>
            Exists.elim hEx fun a h1 =>
              Exists.elim h1 fun b h2 => by
                rw [hC'.2.2 f]
                refine (hFun (Fin.cons Bool.false f)).mpr ⟨a.succ, b, h2.1, Fin.succ_ne_zero a, ?_, ?_⟩
                · rw [hCast a, Fin.cons_succ]; exact h2.2.1
                · rw [hNat b, Fin.cons_succ]; exact h2.2.2))
      hC'.2.1
