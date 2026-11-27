import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_19008_2
    (hForcedSeeds :
      have x1 : Finset ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset;
      have x2 : ℕ := (1099511562240 : ℕ);
      have x3 : ℕ := (1099511627775 : ℕ);
      ∀ (x4 x5 : ℕ) (x6 x7 : Finset ℕ),
        have x8 : Finset ℕ := Insert.insert (x4 ||| (1099511627776 : ℕ)) (Insert.insert (x5 ||| (2199023255552 : ℕ)) x1);
        have x9 : Finset ℕ := Finset.filter (fun z : ℕ => z ≤ x3) x6;
        have x10 : Finset ℕ := Finset.image₂ (fun (a b : ℕ) => a &&& b) x9 x9;
        have x11 : Finset ℕ := Finset.image₂ (fun (a b : ℕ) => a &&& b &&& x3 ||| if (a ||| b) &&& (3298534883328 : ℕ) = (3298534883328 : ℕ) then (1099511627776 : ℕ) else (0 : ℕ)) x6 x6;
        (x4 ∈ x10 ∧ x5 ∈ x10 ∧ x4 &&& x2 ≠ (0 : ℕ) ∧ x4 &&& x5 &&& x2 = (0 : ℕ) ∧
          (∀ w ∈ x6, w < (4398046511104 : ℕ) ∧ w ≠ (0 : ℕ) ∧ ∀ b < (42 : ℕ), w.testBit b = Bool.true → ∃ s ∈ x6 ∩ x8, s ||| w = w ∧ s.testBit b = Bool.true) ∧
          (∃ y ∈ x7, y.testBit (40 : ℕ) = Bool.true) ∧
          (∀ y ∈ x7, y ∈ x11)) →
        (x4 ||| (1099511627776 : ℕ)) ∈ x6 ∧ (x5 ||| (2199023255552 : ℕ)) ∈ x6 ∧ x4 ≤ x3 ∧ x5 ≤ x3 ∧ x4 ≠ x5)
    (hRefuteWithSeeds :
      have x1 : Finset ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset;
      have x2 : ℕ := (1099511562240 : ℕ);
      have x3 : ℕ := (1099511627775 : ℕ);
      ∀ (x4 x5 : ℕ) (x6 x7 : Finset ℕ),
        have x8 : Finset ℕ := Insert.insert (x4 ||| (1099511627776 : ℕ)) (Insert.insert (x5 ||| (2199023255552 : ℕ)) x1);
        have x9 : Finset ℕ := Finset.filter (fun z : ℕ => z ≤ x3) x6;
        have x10 : Finset ℕ := Finset.image₂ (fun (a b : ℕ) => a &&& b) x9 x9;
        have x11 : Finset ℕ := Finset.image₂ (fun (a b : ℕ) => a &&& b &&& x3 ||| if (a ||| b) &&& (3298534883328 : ℕ) = (3298534883328 : ℕ) then (1099511627776 : ℕ) else (0 : ℕ)) x6 x6;
        (x4 ∈ x10 ∧ x5 ∈ x10 ∧ x4 ≤ x3 ∧ x5 ≤ x3 ∧ x4 ≠ x5 ∧
          (x4 ||| (1099511627776 : ℕ)) ∈ x6 ∧ (x5 ||| (2199023255552 : ℕ)) ∈ x6 ∧
          x4 &&& x2 ≠ (0 : ℕ) ∧ x5 &&& x2 ≠ (0 : ℕ) ∧ x4 &&& x5 &&& x2 = (0 : ℕ) ∧
          (∀ w ∈ x6 \ x8, ∃ a ∈ x6, ∃ b ∈ x6, a < w ∧ b < w ∧ w = a ||| b) ∧
          (∀ w ∈ x6, w < (4398046511104 : ℕ) ∧ w ≠ (0 : ℕ) ∧ ∀ b < (42 : ℕ), w.testBit b = Bool.true → ∃ s ∈ x6 ∩ x8, s ||| w = w ∧ s.testBit b = Bool.true) ∧
          (1 : ℕ) ≤ (x6 \ x8).card ∧ (x6 \ x8).card + (2 : ℕ) * x7.card ≤ (20 : ℕ) ∧ x7.card ≤ (9 : ℕ) ∧
          (∀ b ∈ Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)), ∃ y ∈ x7, y.testBit b = Bool.true) ∧
          (∀ y ∈ x7, y ∈ x11 ∧ y &&& x2 = (0 : ℕ) ∧ ∀ z ∈ x11, z &&& x2 = (0 : ℕ) → y ||| z = z → z = y) ∧
          (∀ y ∈ x7, ∃ b < (41 : ℕ), y.testBit b = Bool.true ∧ ∀ z ∈ x7, z.testBit b = Bool.true → z = y)) →
        False) :
    (have x1 : Finset ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset; have x2 : ℕ := (1099511562240 : ℕ); have x3 : ℕ := (1099511627775 : ℕ); ∀ (x4 x5 : ℕ) (x6 x7 : Finset ℕ),   have x8 : Finset ℕ := Insert.insert (x4 ||| (1099511627776 : ℕ)) (Insert.insert (x5 ||| (2199023255552 : ℕ)) x1);   have x9 : Finset ℕ := {x9 ∈ x6 | x9 ≤ x3};   have x10 : Finset ℕ := Finset.image₂ (fun (x10 x11 : ℕ) => x10 &&& x11) x9 x9;   have x11 : Finset ℕ := Finset.image₂ (fun (x11 x12 : ℕ) => x11 &&& x12 &&& x3 ||| if (x11 ||| x12) &&& (3298534883328 : ℕ) = (3298534883328 : ℕ) then (1099511627776 : ℕ) else (0 : ℕ)) x6 x6;   x4 ∈ x10 → x5 ∈ x10 → x4 &&& x2 ≠ (0 : ℕ) → x5 &&& x2 ≠ (0 : ℕ) → x4 &&& x5 &&& x2 = (0 : ℕ) → (∀ x17 ∈ x6 \ x8, ∃ x19 ∈ x6, ∃ x20 ∈ x6, x19 < x17 ∧ x20 < x17 ∧ x17 = x19 ||| x20) → (∀ x18 ∈ x6, x18 < (4398046511104 : ℕ) ∧ x18 ≠ (0 : ℕ) ∧ ∀ x20 < (42 : ℕ), x18.testBit x20 = Bool.true → ∃ x23 ∈ x6 ∩ x8, x23 ||| x18 = x18 ∧ x23.testBit x20 = Bool.true) → (1 : ℕ) ≤ (x6 \ x8).card → (x6 \ x8).card + (2 : ℕ) * x7.card ≤ (20 : ℕ) → x7.card ≤ (9 : ℕ) → (∀ x22 ∈ Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)), ∃ x24 ∈ x7, x24.testBit x22 = Bool.true) → (∀ x23 ∈ x7, x23 ∈ x11 ∧ x23 &&& x2 = (0 : ℕ) ∧ ∀ x25 ∈ x11, x25 &&& x2 = (0 : ℕ) → x23 ||| x25 = x25 → x25 = x23) → (∀ x24 ∈ x7, ∃ x26 < (41 : ℕ), x24.testBit x26 = Bool.true ∧ ∀ x27 ∈ x7, x27.testBit x26 = Bool.true → x27 = x24) → False) :=
  fun x4 x5 x6 x7 h1 h2 h3 h4 h5 hDag hSub hC1 hC20 hC9 hCov hMax hUniq =>
    have hs := hForcedSeeds x4 x5 x6 x7 ⟨h1, h2, h3, h5, hSub, hCov (40 : ℕ) (Finset.mem_insert_self _ _), fun y hy => (hMax y hy).1⟩
    hRefuteWithSeeds x4 x5 x6 x7 ⟨h1, h2, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, hs.1, hs.2.1, h3, h4, h5, hDag, hSub, hC1, hC20, hC9, hCov, hMax, hUniq⟩
