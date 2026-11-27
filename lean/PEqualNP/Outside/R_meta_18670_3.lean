import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18670_3
    (hStarCircuit :
      have stars : List (ℕ × List ℕ) :=
        [(0, [12, 14, 20]), (1, [13, 19, 23]), (2, [12, 18, 22, 23]), (3, [17, 21, 22]),
         (4, [16, 20, 21, 23]), (5, [15, 19, 20, 22]), (6, [14, 18, 19, 21]), (7, [13, 17, 18, 20]),
         (8, [12, 16, 17, 19]), (9, [14, 15, 17, 23]), (10, [13, 14, 16, 22]), (11, [12, 13, 15, 21])];
      have f : (Fin (24 : ℕ) → Bool) → Bool := fun x =>
        stars.any fun s => x (Fin.ofNat (24 : ℕ) s.1) && s.2.any fun j => x (Fin.ofNat (24 : ℕ) j);
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w0 w1 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (58 : ℕ) ∧
        C.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧
        Max.max C.output (Max.max w0 w1) < (24 : ℕ) + C.size ∧
        ∀ (x : Fin (24 : ℕ) → Bool),
          C.eval (List.ofFn x) = f x ∧
          (f x = Bool.false →
            (C.wires (List.ofFn x)).getD w0 Bool.false = (x (0 : Fin (24 : ℕ)) || x (1 : Fin (24 : ℕ)) || x (3 : Fin (24 : ℕ))) ∧
            (C.wires (List.ofFn x)).getD w1 Bool.false = (x (15 : Fin (24 : ℕ)) || x (16 : Fin (24 : ℕ)) || x (18 : Fin (24 : ℕ)))))
    (hStarEquiv :
      have stars : List (ℕ × List ℕ) :=
        [(0, [12, 14, 20]), (1, [13, 19, 23]), (2, [12, 18, 22, 23]), (3, [17, 21, 22]),
         (4, [16, 20, 21, 23]), (5, [15, 19, 20, 22]), (6, [14, 18, 19, 21]), (7, [13, 17, 18, 20]),
         (8, [12, 16, 17, 19]), (9, [14, 15, 17, 23]), (10, [13, 14, 16, 22]), (11, [12, 13, 15, 21])];
      ∀ (x : Fin (24 : ℕ) → Bool),
        (stars.any fun s => x (Fin.ofNat (24 : ℕ) s.1) && s.2.any fun j => x (Fin.ofNat (24 : ℕ) j)) = Bool.true ↔
        ∃ (u v : Fin (12 : ℕ)),
          (Fin.succAbove (9 : Fin (13 : ℕ)) u + Fin.succAbove (0 : Fin (13 : ℕ)) v : Fin (13 : ℕ)) ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] ∧
          x (Fin.castAdd (12 : ℕ) u) = Bool.true ∧
          x (Fin.natAdd (12 : ℕ) v) = Bool.true) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop := fun (x2 x3 : Fin (12 : ℕ)) => Fin.succAbove (9 : Fin (13 : ℕ)) x2 + Fin.succAbove (0 : Fin (13 : ℕ)) x3 ∈ x1; have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x2 x5 x4 → x3 x5 = Bool.false); have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x2 x5 x6 → x4 x6 = Bool.false); have x5 : Bool → Finset (Fin (24 : ℕ)) := fun (x5 : Bool) => if x5 = Bool.true then {(15 : Fin (24 : ℕ)), (16 : Fin (24 : ℕ)), (18 : Fin (24 : ℕ))} else {(0 : Fin (24 : ℕ)), (1 : Fin (24 : ℕ)), (3 : Fin (24 : ℕ))}; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x6 ∧     x6.size ≤ (58 : ℕ) ∧       x6.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧         Max.max x6.output (Max.max x7 x8) < (24 : ℕ) + x6.size ∧           (∀ (x9 x10 : Fin (12 : ℕ)), x2 x9 x10 → x6.eval (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (12 : ℕ) x9 ∨ x12 = Fin.natAdd (12 : ℕ) x10)) = Bool.true) ∧             (∀ (x9 : Bool), ∀ x10 ∈ x5 x9, (x6.wires (List.ofFn fun (x12 : Fin (24 : ℕ)) => Decidable.decide (x12 = x10))).getD (if x9 = Bool.true then x8 else x7) Bool.false = Bool.true) ∧               ∀ (x9 : Fin (12 : ℕ) → Bool),                 x4 (x3 x9) = x9 →                   have x11 : Fin (24 : ℕ) → Bool := Fin.append x9 (x3 x9);                   x6.eval (List.ofFn x11) = Bool.false ∧ ∀ (x12 : Bool), (x6.wires (List.ofFn fun (x13 : Fin (24 : ℕ)) => if x13 ∈ x5 x12 then Bool.false else x11 x13)).getD (if x12 = Bool.true then x8 else x7) Bool.false = Bool.false) := by
  intro x1 x2 x3 x4 x5
  let stars : List (ℕ × List ℕ) :=
    [(0, [12, 14, 20]), (1, [13, 19, 23]), (2, [12, 18, 22, 23]), (3, [17, 21, 22]),
     (4, [16, 20, 21, 23]), (5, [15, 19, 20, 22]), (6, [14, 18, 19, 21]), (7, [13, 17, 18, 20]),
     (8, [12, 16, 17, 19]), (9, [14, 15, 17, 23]), (10, [13, 14, 16, 22]), (11, [12, 13, 15, 21])]
  let star12 : (Fin (24 : ℕ) → Bool) → Bool := fun x =>
    stars.any fun s => x (Fin.ofNat (24 : ℕ) s.1) && s.2.any fun j => x (Fin.ofNat (24 : ℕ) j)
  let mem_to : ∀ {z : Fin (13 : ℕ)},
      z ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] →
      z ∈ x1 := fun h =>
    Or.elim (List.mem_cons.mp h) (fun h => Finset.mem_insert.mpr (Or.inl h)) fun h =>
    Or.elim (List.mem_cons.mp h) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))) fun h =>
    Or.elim (List.mem_cons.mp h) (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))))) fun h =>
    Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (List.mem_singleton.mp h)))))))
  let mem_of : ∀ {z : Fin (13 : ℕ)},
      z ∈ x1 →
      z ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))] := fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => h ▸ List.Mem.head _) fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => h ▸ List.Mem.tail _ (List.Mem.head _)) fun h =>
    Or.elim (Finset.mem_insert.mp h) (fun h => h ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) fun h =>
    (Finset.mem_singleton.mp h) ▸ List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  refine Exists.elim hStarCircuit fun C hC => Exists.elim hC fun w0 hw0 => Exists.elim hw0 fun w1 h => ?_
  refine ⟨C, w0, w1, h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_⟩
  · intro u v huv
    let vp : Fin (24 : ℕ) → Bool := fun x12 => Decidable.decide (x12 = Fin.castAdd (12 : ℕ) u ∨ x12 = Fin.natAdd (12 : ℕ) v)
    exact Eq.trans (h.2.2.2.2 vp).1
      ((hStarEquiv vp).mpr ⟨u, v, mem_of huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩)
  · intro b k hk
    let vs : Fin (24 : ℕ) → Bool := fun j => Decidable.decide (j = k)
    have hf : star12 vs = Bool.false :=
      Bool.eq_false_iff.mpr fun ht =>
        Exists.elim ((hStarEquiv vs).mp ht) fun u hu =>
          Exists.elim hu fun v hv =>
            let h1 : Fin.castAdd (12 : ℕ) u = k := of_decide_eq_true hv.2.1
            let h2 : Fin.natAdd (12 : ℕ) v = k := of_decide_eq_true hv.2.2
            let hval : (u : ℕ) = (12 : ℕ) + (v : ℕ) := congrArg Fin.val (Eq.trans h1 h2.symm)
            Nat.not_lt.mpr (hval ▸ Nat.le_add_right (12 : ℕ) (v : ℕ)) u.isLt
    cases b
    · have hk' : k ∈ ({(0 : Fin (24 : ℕ)), (1 : Fin (24 : ℕ)), (3 : Fin (24 : ℕ))} : Finset (Fin (24 : ℕ))) :=
        Eq.mp (congrArg (k ∈ ·) (if_neg Bool.false_ne_true)) hk
      rw [if_neg Bool.false_ne_true]
      have hval := ((h.2.2.2.2 vs).2 hf).1
      exact Or.elim (Finset.mem_insert.mp hk')
        (fun h0 =>
          let ht : vs (0 : Fin (24 : ℕ)) = Bool.true := decide_eq_true h0.symm
          Eq.trans hval (Eq.trans (congrArg (fun t => (t || _) || _) ht) (Eq.trans (congrArg (· || _) (Bool.true_or _)) (Bool.true_or _))))
        fun hk1 =>
          Or.elim (Finset.mem_insert.mp hk1)
            (fun h1 =>
              let ht : vs (1 : Fin (24 : ℕ)) = Bool.true := decide_eq_true h1.symm
              Eq.trans hval (Eq.trans (congrArg (fun t => (_ || t) || _) ht) (Eq.trans (congrArg (· || _) (Bool.or_true _)) (Bool.true_or _))))
            (fun hk2 =>
              let ht : vs (3 : Fin (24 : ℕ)) = Bool.true := decide_eq_true (Finset.mem_singleton.mp hk2).symm
              Eq.trans hval (Eq.trans (congrArg (_ || ·) ht) (Bool.or_true _)))
    · have hk' : k ∈ ({(15 : Fin (24 : ℕ)), (16 : Fin (24 : ℕ)), (18 : Fin (24 : ℕ))} : Finset (Fin (24 : ℕ))) :=
        Eq.mp (congrArg (k ∈ ·) (if_pos rfl)) hk
      rw [if_pos rfl]
      have hval := ((h.2.2.2.2 vs).2 hf).2
      exact Or.elim (Finset.mem_insert.mp hk')
        (fun h15 =>
          let ht : vs (15 : Fin (24 : ℕ)) = Bool.true := decide_eq_true h15.symm
          Eq.trans hval (Eq.trans (congrArg (fun t => (t || _) || _) ht) (Eq.trans (congrArg (· || _) (Bool.true_or _)) (Bool.true_or _))))
        fun hk1 =>
          Or.elim (Finset.mem_insert.mp hk1)
            (fun h16 =>
              let ht : vs (16 : Fin (24 : ℕ)) = Bool.true := decide_eq_true h16.symm
              Eq.trans hval (Eq.trans (congrArg (fun t => (_ || t) || _) ht) (Eq.trans (congrArg (· || _) (Bool.or_true _)) (Bool.true_or _))))
            (fun hk2 =>
              let ht : vs (18 : Fin (24 : ℕ)) = Bool.true := decide_eq_true (Finset.mem_singleton.mp hk2).symm
              Eq.trans hval (Eq.trans (congrArg (_ || ·) ht) (Bool.or_true _)))
  · intro a _
    let x11 : Fin (24 : ℕ) → Bool := Fin.append a (x3 a)
    have hf11 : star12 x11 = Bool.false :=
      Bool.eq_false_iff.mpr fun ht =>
        Exists.elim ((hStarEquiv x11).mp ht) fun u hu =>
          Exists.elim hu fun v hv =>
            let hau : a u = Bool.true := Eq.trans (Fin.append_left a (x3 a) u).symm hv.2.1
            let hbv : x3 a v = Bool.true := Eq.trans (Fin.append_right a (x3 a) v).symm hv.2.2
            Bool.false_ne_true (Eq.trans ((of_decide_eq_true hbv) u (mem_to hv.1)).symm hau)
    refine ⟨Eq.trans (h.2.2.2.2 x11).1 hf11, fun b => ?_⟩
    let x13 : Fin (24 : ℕ) → Bool := fun k => if k ∈ x5 b then Bool.false else x11 k
    have hle : ∀ (k : Fin (24 : ℕ)), x13 k = Bool.true → x11 k = Bool.true := fun k hk =>
      Or.elim (Decidable.em (k ∈ x5 b))
        (fun hm => False.elim (Bool.false_ne_true (Eq.trans (if_pos hm).symm hk)))
        (fun hnm => Eq.trans (if_neg hnm).symm hk)
    have hf13 : star12 x13 = Bool.false :=
      Bool.eq_false_iff.mpr fun ht =>
        Exists.elim ((hStarEquiv x13).mp ht) fun u hu =>
          Exists.elim hu fun v hv =>
            Bool.false_ne_true (Eq.trans hf11.symm ((hStarEquiv x11).mpr ⟨u, v, hv.1, hle _ hv.2.1, hle _ hv.2.2⟩))
    cases b
    · rw [if_neg Bool.false_ne_true]
      have hval := ((h.2.2.2.2 x13).2 hf13).1
      have h0 : x13 (0 : Fin (24 : ℕ)) = Bool.false :=
        if_pos (Eq.mpr (congrArg ((0 : Fin (24 : ℕ)) ∈ ·) (if_neg Bool.false_ne_true)) (Finset.mem_insert_self _ _))
      have h1 : x13 (1 : Fin (24 : ℕ)) = Bool.false :=
        if_pos (Eq.mpr (congrArg ((1 : Fin (24 : ℕ)) ∈ ·) (if_neg Bool.false_ne_true)) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      have h3 : x13 (3 : Fin (24 : ℕ)) = Bool.false :=
        if_pos (Eq.mpr (congrArg ((3 : Fin (24 : ℕ)) ∈ ·) (if_neg Bool.false_ne_true)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      exact Eq.trans hval (congrArg₂ or (congrArg₂ or h0 h1) h3)
    · rw [if_pos rfl]
      have hval := ((h.2.2.2.2 x13).2 hf13).2
      have h15 : x13 (15 : Fin (24 : ℕ)) = Bool.false :=
        if_pos (Eq.mpr (congrArg ((15 : Fin (24 : ℕ)) ∈ ·) (if_pos rfl)) (Finset.mem_insert_self _ _))
      have h16 : x13 (16 : Fin (24 : ℕ)) = Bool.false :=
        if_pos (Eq.mpr (congrArg ((16 : Fin (24 : ℕ)) ∈ ·) (if_pos rfl)) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      have h18 : x13 (18 : Fin (24 : ℕ)) = Bool.false :=
        if_pos (Eq.mpr (congrArg ((18 : Fin (24 : ℕ)) ∈ ·) (if_pos rfl)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      exact Eq.trans hval (congrArg₂ or (congrArg₂ or h15 h16) h18)
