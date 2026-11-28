import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38753

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808426 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x68000904490e2362#64 ++ 0xb4000482248711b1#64 ++ 0xf5809f3cfb1e67e7#64 ++ 0xfac04f9e7d8f33f3#64 : BitVec 256),
   (0x100324512060c88d#64 ++ 0x0801922890306446#64 ++ 0xef8764d324e3f8ff#64 ++ 0xf7c3b2699271fc7f#64 : BitVec 256),
   (0xa03858a2c7031530#64 ++ 0x501c2c5163818a98#64 ++ 0xdef878e3c7039f39#64 ++ 0xef7c3c71e381cf9c#64 : BitVec 256),
   (0xc0dd80fc06b41ec0#64 ++ 0x606ec07e035a0f60#64 ++ 0xbfff80fc07fc1fc1#64 ++ 0x5fffc07e03fe0fe0#64 : BitVec 256),
   (0x016eff0007dbe001#64 ++ 0x80b77f8003edf000#64 ++ 0x7f7fff0007ffe001#64 ++ 0x3fbfff8003fff000#64 : BitVec 256),
   (0x0077f6fbb0000000#64 ++ 0x003bfb7dd8000000#64 ++ 0xfc7ffffff8000000#64 ++ 0xfe3ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1 : W := mkw 0x01080900079b2000 0x8084048003cd9000 0x00000000031c0000 0x00000000018e0000

def z2 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z3 : W := mkw 0x100324512060c88d 0x0801922890306446 0xef8764d324e3f8ff 0xf7c3b2699271fc7f

def z4 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xf5809f3cfb1e67e7 0xfac04f9e7d8f33f3

def z5 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdef878e3c7039f39 0xef7c3c71e381cf9c

def z6 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z7 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfffffffffce3f8ff 0xfffffffffe71fc7f

def z8 : W := mkw 0xc088000406b41ec0 0x60440002035a0f60 0x0380000007fc1fc1 0x01c0000003fe0fe0

def z9 : W := mkw 0xe8dd89fc4fbe3fe2 0xf46ec4fe27df1ff1 0xffff9ffcfffe7fe7 0xffffcffe7fff3ff3

def z10 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x808000fc00001fc0 0x4040007e00000fe0

def z11 : W := mkw 0xd09324fd2064decd 0x6849927e90326f66 0xef8764ff24e3ffff 0xf7c3b27f9271ffff

def z12 : W := mkw 0x48000104080c2242 0xa400008204061121 0x2100871c381c60c6 0x1080438e1c0e3063

def z13 : W := mkw 0x50c7a45d20f4cacd 0x2863d22e907a6566 0x2107841c20fc60c6 0x1083c20e107e3063

def z14 : W := mkw 0xd0dfa4fd26f4decd 0x686fd27e937a6f66 0xffffe4ff27ffffff 0xfffff27f93ffffff

def z15 : W := mkw 0x803850a286011410 0x401c285143008a08 0x0a7860c304019818 0x053c30618200cc0c

def z16 : W := mkw 0xa17ffffbf7dbf531 0xd0bffffdfbedfa98 0xffffffffffffff39 0xffffffffffffff9c

def z17 : W := mkw 0x6877fffff90e2362 0xb43bfffffc8711b1 0xfdfffffffb1e67e7 0xfefffffffd8f33f3

def z18 : W := mkw 0x1047a6593060c88d 0x0823d32c98306446 0x2107871c38e060c6 0x1083c38e1c703063

def z19 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x10789b00031c0000 0x083c4d80018e0000

def z20 : W := mkw 0x100100512020088c 0x0800802890100446 0x808000d3200018fe 0xc040006990000c7f

def z21 : W := mkw 0x004c800006900000 0x0026400003480000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z22 : W := mkw 0xe0fdd8fec7b71ff0 0x707eec7f63db8ff8 0xfffff8ffc7ff9ff9 0xfffffc7fe3ffcffc

def z23 : W := mkw 0x005580f800000000 0x002ac07c00000000 0xfc7f9ffcf8000000 0xfe3fcffe7c000000

def z24 : W := mkw 0x005580f800000000 0x002ac07c00000000 0x087f00c000000000 0x043f806000000000

def z25 : W := mkw 0x016eff03b7dbe001 0x80b77f81dbedf000 0x7f7fff03ffffe001 0xbfbfff81fffff000

def z26 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0x1078802c031c0700 0x083c4016018e0380

def z27 : W := mkw 0xb03a7ca3e743d53d 0x581d3e51f3a1ea9e 0xdef87ce3e703ff3f 0xef7c3e71f381ff9f

def z28 : W := mkw 0x903b74f3a661dc9d 0x481dba79d330ee4e 0xefff64d324e3f8ff 0xf7ffb2699271fc7f

def z29 : W := mkw 0x0066f60000000000 0x00337b0000000000 0x7c7fff0000000000 0x3e3fff8000000000

def z30 : W := mkw 0x0108090007dbe001 0x8084048003edf000 0x0300000007ffe001 0x0180000003fff000

def z31 : W := mkw 0x0066f6000040c001 0x00337b0000206000 0x7f7fff0004e3e001 0x3fbfff800271f000

def z32 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x10789b2cd8000000 0x083c4d966c000000

def z33 : W := mkw 0xc089005406b41ec0 0x6044802a035a0f60 0xaf8700d007fc1fc1 0x57c3806803fe0fe0

def z34 : W := mkw 0xa008080047031530 0x5004040023818a98 0xce8060c307039f39 0xe74030618381cf9c

def z35 : W := mkw 0x696cdb044f9f2362 0xb4b66d8227cf91b1 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z36 : W := mkw 0x28000900490a2122 0x9400048024851091 0x40001f00f8026026 0xa0000f807c013013

def z37 : W := mkw 0x01227f00014be001 0x80913f8000a5f000 0x40007f000003e000 0x20003f800001f000

def z38 : W := mkw 0x801800a006001400 0x400c005003000a00 0x9ef800e007001f01 0x4f7c007003800f80

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0xce8060c304039839 0xe74030618201cc1c

def z40 : W := mkw 0xb03b7cf3e763ddbd 0x581dbe79f3b1eede 0xffff7cf3e7e3ffff 0xffffbe79f3f1ffff

def z41 : W := mkw 0x4877f7ffb80c2242 0xa43bfbffdc061121 0xfd7ffffff81c60c6 0xfebffffffc0e3063

def z42 : W := mkw 0xb07ffefbf763ddbd 0x583fff7dfbb1eede 0xffffffffffe3ffff 0xfffffffffff1ffff

def z43 : W := mkw 0x690809044fdfe363 0xb484048227eff1b1 0x0380000007ffe7e7 0x01c0000003fff3f3

def z44 : W := mkw 0xc1fffffc07fffec1 0xe0fffffe03ffff60 0xfffffffc07ffffc1 0x7ffffffe03ffffe0

def z45 : W := mkw 0xb00808004763ddbd 0x5804040023b1eede 0x0380000007e3ffff 0x01c0000003f1ffff

def z46 : W := mkw 0x100324512060c88d 0x0801922890306446 0xaf8704d024e078c7 0x57c3826812703c63

def z47 : W := mkw 0x7877fffff96eebef 0xbc3bfffffcb775f7 0xffffffffffffffff 0xffffffffffffffff

def z48 : W := mkw 0x0047a65930000000 0x0023d32c98000000 0x2007871c38000000 0x1003c38e1c000000

def z49 : W := mkw 0xc09900fc06241ec0 0x604c807e03120f60 0x9ef800fc07001fc1 0x4f7c007e03800fe0

def z50 : W := mkw 0x100324512060c88d 0x0801922890306446 0x0a0760c304e19818 0x0503b0618270cc0c

def z51 : W := mkw 0x100324512060c88d 0x0801922890306446 0x0007000000e00000 0x0003800000700000

def z52 : W := mkw 0x001100fbb0000000 0x0008807dd8000000 0x800000fff8000000 0xc000007ffc000000

def z53 : W := mkw 0x21227f02c14be131 0x90913f8160a5f098 0x40007f03c003e038 0xa0003f81e001f01c

def z54 : W := mkw 0xa17effa2c7dbf531 0xd0bf7fd163edfa98 0xffffffe3c7ffff39 0xfffffff1e3ffff9c

def z55 : W := mkw 0x40cd805c06b40ac0 0x2066c02e035a0560 0x3f7f801c07fc00c1 0x1fbfc00e03fe0060

def z56 : W := mkw 0x0146a70000d8e001 0x80a35380006c7000 0x2107870000fc6000 0x1083c380007e3000

def z57 : W := mkw 0xd0fff6ffb6f4decd 0x687ffb7fdb7a6f66 0xffffffffffffffff 0xffffffffffffffff

def z58 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff9ffcfffc1fc1 0xffffcffe7ffe0fe0

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0xf4009f3cf8000000 0xfa004f9e7c000000

def z60 : W := mkw 0x003050a280000000 0x0018285140000000 0xdc7878e3c0000000 0xee3c3c71e0000000

def z61 : W := mkw 0x28227f03f90a2122 0x94113f81fc851091 0x40007f03f8026026 0xa0003f81fc013013

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x2f07000004e00001 0x1783800002700000

def z63 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x187ffbefd8000000 0x0c3ffdf7ec000000

def z64 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000040020026026 0xa000020010013013

def z65 : W := mkw 0x496eff040fdfe243 0xa4b77f8207eff121 0x7f7fff1c3fffe0c7 0x3fbfff8e1ffff063

def z66 : W := mkw 0x4000000400040240 0x2000000200020120 0xb580803c031c07c1 0x5ac0401e018e03e0

def z67 : W := mkw 0xa07cdaaad7031530 0x503e6d556b818a98 0xdef8fbefdf039f39 0xef7c7df7ef81cf9c

def z68 : W := mkw 0x0044800000900000 0x0022400000480000 0x2107800000fc0000 0x1083c000007e0000

def z69 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x31009f3cfb1c67c6 0x18804f9e7d8e33e3

def z70 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x11809b2cdb1e67e7 0x08c04d966d8f33f3

def z71 : W := mkw 0xa03b7cf3e7031530 0x501dbe79f3818a98 0xfeff7cf3e7039f39 0xff7fbe79f381cf9c

def z72 : W := mkw 0x78010955692e2bee 0xbc0084aab49715f7 0xf5809ffffb1e7fff 0xfac04ffffd8f3fff

def z73 : W := mkw 0xc1fcdbac079f3640 0xe0fe6dd603cf9b20 0x10789b2c031c0700 0x083c4d96018e0380

def z74 : W := mkw 0x4080000400b40ac0 0x20400002005a0560 0x0100000000fc00c0 0x00800000007e0060

def z75 : W := mkw 0x100324512060c88d 0x0801922890306446 0xc08064d32003f8fe 0xe04032699001fc7f

def z76 : W := mkw 0xe83859a6cf0f3772 0xf41c2cd367879bb9 0xfff8ffffff1fffff 0xfffc7fffff8fffff

def z77 : W := mkw 0x1077f6fbb040c00d 0x083bfb7dd8206006 0xfc7ffffff803e03e 0xfe3ffffffc01f01f

def z78 : W := mkw 0xc088000406b41ec0 0x60440002035a0f60 0xb780803c07fc1fc1 0x5bc0401e03fe0fe0

def z79 : W := mkw 0x005580f800000000 0x002ac07c00000000 0xbc7f80fc00000000 0x5e3fc07e00000000

def z80 : W := mkw 0xc0fff6ffb6b41ec0 0x607ffb7fdb5a0f60 0xfffffffffffc1fc1 0xfffffffffffe0fe0

def z81 : W := mkw 0x10032d51216ae88d 0x880196a890b57446 0xff87ffd327fff8ff 0xffc3ffe993fffc7f

def z82 : W := mkw 0x817ef6a286d1d411 0x40bf7b514368ea08 0x0a7f60c304e19818 0x053fb0618270cc0c

def z83 : W := mkw 0xa01000a2c0001530 0x5008005160000a98 0x808000e3c0001f38 0xc0400071e0000f9c

def z84 : W := mkw 0x100224012040c00d 0x0801120090206006 0x400064032003e03e 0xa00032019001f01f

def z85 : W := mkw 0x2000080041030130 0x1000040020818098 0x0000000000038038 0x000000000001c01c

def z86 : W := mkw 0xe1fffffec7fffff1 0xf0ffffff63fffff8 0xffffffffc7fffff9 0xffffffffe3fffffc

def z87 : W := mkw 0x0177fffbb14be001 0x80bbfffdd8a5f000 0xfc7ffffff803e000 0xfe3ffffffc01f000

def z88 : W := mkw 0xe80809044f0f3772 0xf404048227879bb9 0x03800000071fffff 0x01c00000038fffff

def z89 : W := mkw 0x80dd80f806b01c80 0x406ec07c03580e40 0x0a7f00c004e01800 0x053f806002700c00

def z90 : W := mkw 0x100324512060c88d 0x0801922890306446 0xa18704d320e078fe 0xd0c3826990703c7f

def z91 : W := mkw 0x69227f04494fe363 0xb4913f8224a7f1b1 0xf580ff3cfb1fe7e7 0xfac07f9e7d8ff3f3

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0xe5800410200260e7 0xf2c0020810013073

def z93 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff84fc27fe7fe7 0xffffc27e13ff3ff3

def z94 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x50009f2cfb1e6726 0xa8004f967d8f3393

def z95 : W := mkw 0x0166ff0001dbe001 0x80b37f8000edf000 0x6107ff0000ffe000 0x3083ff80007ff000

def z96 : W := mkw 0x0147a75930d8e001 0x80a3d3ac986c7000 0x2107871c38fc6000 0x1083c38e1c7e3000

def z97 : W := mkw 0xc0dd80ffb6b41ec0 0x606ec07fdb5a0f60 0xbfff80fffffc1fc1 0xdfffc07ffffe0fe0

def z98 : W := mkw 0x78032d55696eebef 0xbc0196aab4b775f7 0xff87ffffffffffff 0xffc3ffffffffffff

def z99 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x317f803c03fc07c0 0x18bfc01e01fe03e0

def z100 : W := mkw 0x00227603b0000000 0x00113b01d8000000 0xf400ff3ff8000000 0xfa007f9ffc000000

def z101 : W := mkw 0xc0fdd2fe96b41ec0 0x607ee97f4b5a0f60 0xbfff9bfcdffc1fc1 0x5fffcdfe6ffe0fe0

def z102 : W := mkw 0xa07ffefbf7031530 0x503fff7dfb818a98 0xfeffffffff039f39 0xff7fffffff81cf9c

def z103 : W := mkw 0x801800a006001400 0x400c005003000a00 0xdef860e307039f39 0xef7c30718381cf9c

def z104 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0xbc7f9bfcd8000000 0x5e3fcdfe6c000000

def z105 : W := mkw 0x100324512060c88d 0x0801922890306446 0xe587041020e260e7 0xf2c3820810713073

def z106 : W := mkw 0x11237f51216be88d 0x8891bfa890b5f446 0xef877fd324e3f8ff 0xf7c3bfe99271fc7f

def z107 : W := mkw 0xe8dd89fc4fbe3fe2 0xf46ec4fe27df1ff1 0xbfff9bfcdffc1fc1 0x5fffcdfe6ffe0fe0

def z108 : W := mkw 0xd09100fd20241ecc 0x6848807e90120f66 0x808000ff20001ffe 0xc040007f90000fff

def z109 : W := mkw 0x0000000000000000 0x0000000000000000 0xef8064d32403f8ff 0xf7c032699201fc7f

def z110 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x3f7fe00007fd8001 0x1fbff00003fec000

def z111 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x0078000000000000 0x003c000000000000

def z112 : W := mkw 0xa01100fbf0001530 0x5008807df8000a98 0x808000fff8001f38 0xc040007ffc000f9c

def z113 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x317f9f0003fc6000 0x18bfcf8001fe3000

def z114 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x9ef818e0c7001f01 0x4f7c0c7063800f80

def z115 : W := mkw 0x296eff004fdbe123 0x94b77f8027edf091 0x7f7fff00ffffe027 0xbfbfff807ffff013

def z116 : W := mkw 0x00000900010a2000 0x8000048000851000 0x75009f00031e6001 0x3a804f80018f3000

def z117 : W := mkw 0x0028580007030000 0x00142c0003818000 0x5e78780007038001 0x2f3c3c000381c000

def z118 : W := mkw 0xc0dc80ac06b41ec0 0x606e4056035a0f60 0x13f8802c07fc1fc1 0x09fc401603fe0fe0

def z119 : W := mkw 0xa008080047031530 0x5004040023818a98 0x0000000003000700 0x0000000001800380

def z120 : W := mkw 0x29227f00494be123 0x94913f8024a5f091 0x40007f00f803e026 0xa0003f807c01f013

def z121 : W := mkw 0x40c5805c00b40ac0 0x2062c02e005a0560 0x2107801c00fc00c0 0x1083c00e007e0060

def z122 : W := mkw 0x28205902c90b2132 0x94102c8164859099 0x40007f03f803e03e 0xa0003f81fc01f01f

def z123 : W := mkw 0x116fff5127fbe88d 0x88b7ffa893fdf446 0xffffffd327fff8ff 0xffffffe993fffc7f

def z124 : W := mkw 0xa07cd8a2c7931530 0x503e6c5163c98a98 0xfffff8e3c7ff9f39 0xfffffc71e3ffcf9c

def z125 : W := mkw 0x0002240120000000 0x0001120090000000 0x4000640320000000 0xa000320190000000

def z126 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x0b7f600007ffe001 0x05bfb00003fff000

def z127 : W := mkw 0x100324512040c00d 0x0801922890206006 0xec0764d32003e03e 0xf603b2699001f01f

def z128 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x0a7f600004e18000 0x053fb0000270c000

def z129 : W := mkw 0x004c800006900000 0x0026400003480000 0x0a7f000004e00000 0x053f800002700000

def z130 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x10009b2cdb1c0700 0x08004d966d8e0380

def z131 : W := mkw 0x0001005000200880 0x0000802800100440 0xaf8700d004e018c1 0x57c3806802700c60

def z132 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfef8ffffff039f39 0xff7c7fffff81cf9c

def z133 : W := mkw 0x00227603b0000000 0x00113b01d8000000 0x40007f03f8000000 0xa0003f81fc000000

def z134 : W := mkw 0xe88809044fbe3fe2 0xf444048227df1ff1 0xf7809f3cfffe7fe7 0xfbc04f9e7fff3ff3

def z135 : W := mkw 0x696eff044fdfe363 0xb4b77f8227eff1b1 0x7f7fff2cdfffe701 0x3fbfff966ffff380

def z136 : W := mkw 0x012a7f00074be001 0x80953f8003a5f000 0x5e787f000703e001 0x2f3c3f800381f000

def z137 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xdc78fbefd8000000 0xee3c7df7ec000000

def z138 : W := mkw 0x801800a006001400 0x400c005003000a00 0x0a7800c004001800 0x053c006002000c00

def z139 : W := mkw 0x0003245120000000 0x0001922890000000 0xec0764d320000000 0xf603b26990000000

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0xf5809f3cf80260e7 0xfac04f9e7c013073

def z141 : W := mkw 0xb00b2c516763ddbd 0x58059628b3b1eede 0xef8764d327e3ffff 0xf7c3b26993f1ffff

def z142 : W := mkw 0xc088000406941640 0x60440002034a0b20 0x00000000031c0700 0x00000000018e0380

def z143 : W := mkw 0x0044820810000000 0x0022410408000000 0x0000830c18000000 0x000041860c000000

def z144 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x01800000031e67e7 0x00c00000018f33f3

def z145 : W := mkw 0x0000000000000000 0x0000000000000000 0x01800000000260e7 0x00c0000000013073

def z146 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xc0801f3cf80267e6 0xe0400f9e7c0133f3

def z147 : W := mkw 0x004c8900079a2000 0x8026448003cd1000 0x7f7f9f0007fe6001 0x3fbfcf8003ff3000

def z148 : W := mkw 0x000224000040c001 0x0001120000206000 0x6f07640004e3e001 0x3783b2000271f000

def z149 : W := mkw 0x0075d2fbb0000000 0x003ae97dd8000000 0x90789bfff8000000 0xc83c4dfffc000000

def z150 : W := mkw 0xc09000ac00041640 0x6048005600020b20 0x0000002c00000700 0x0000001600000380

def z151 : W := mkw 0x116fff5127fbe88d 0x88b7ffa893fdf446 0x7f7fffc307fff819 0x3fbfffe183fffc0c

def z152 : W := mkw 0x100324512060c88d 0x0801922890306446 0xff87fffffce3f8ff 0xffc3fffffe71fc7f

def z153 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x2180871c3b1e67e7 0x10c0438e1d8f33f3

def z154 : W := mkw 0xc0cd805c06b41ec0 0x6066c02e035a0f60 0x2387801c07fc1fc1 0x11c3c00e03fe0fe0

def z155 : W := mkw 0x2000080041020120 0x1000040020810090 0xd4801820c3020721 0xea400c1061810390

def z156 : W := mkw 0x100100512020088c 0x0800802890100446 0x00000010200000c6 0x0000000810000063

def z157 : W := mkw 0x010227000048e001 0x8081138000247000 0x0000070000006000 0x0000038000003000

def z158 : W := mkw 0xe8dc89ac4f9e3762 0xf46e44d627cf1bb1 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z159 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xff80ffffff1fffff 0xffc07fffff8fffff

def z160 : W := mkw 0x006cd80007930000 0x00366c0003c98000 0x7f7ff80007ff8001 0x3fbffc0003ffc000

def z161 : W := mkw 0x68c5895c49be2be2 0xb462c4ae24df15f1 0xf5879f3cfbfe67e7 0xfac3cf9e7dff33f3

def z162 : W := mkw 0xa008080047031530 0x5004040023818a98 0x0280000007039f39 0x014000000381cf9c

def z163 : W := mkw 0xc0dd89fc07be3ec0 0xe06ec4fe03df1f60 0xffff9ffc07fe7fc1 0x7fffcffe03ff3fe0

def z164 : W := mkw 0x0001005000200880 0x0000802800100440 0x808000d0000018c0 0x4040006800000c60

def z165 : W := mkw 0x40c5805c00b40ac0 0x2062c02e005a0560 0xb587803c03fc07c1 0x5ac3c01e01fe03e0

def z166 : W := mkw 0x0008080007030000 0x0004040003818000 0x0200000007038001 0x010000000381c000

def z167 : W := mkw 0x8008000006001400 0x4004000003000a00 0x0280000007001f01 0x0140000003800f80

def z168 : W := mkw 0xe0b858a6c7b71ff0 0x705c2c5363db8ff8 0xdff878e3c7ff9ff9 0xeffc3c71e3ffcffc

def z169 : W := mkw 0x0066f60000000000 0x00337b0000000000 0xfc7fff3cf8000000 0xfe3fff9e7c000000

def z170 : W := mkw 0x4000000400040240 0x2000000200020120 0x8080003c000007c0 0x4040001e000003e0

def z171 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x1a7878e3c7019f18 0x0d3c3c71e380cf8c

def z172 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfd7ffffff8e060c6 0xfebffffffc703063

def z173 : W := mkw 0xe88809044fbe3fe2 0xf444048227df1ff1 0x0380000007fe7fe7 0x01c0000003ff3ff3

def z174 : W := mkw 0x0003245120000000 0x0001922890000000 0xed8764d3200260e7 0xf6c3b26990013073

def z175 : W := mkw 0x116ff65126f1c88d 0x08b7fb289378e446 0xefff64d324e3f8ff 0xf7ffb2699271fc7f

def z176 : W := mkw 0x0001005120000000 0x0000802890000000 0x800000d320000000 0xc000006990000000

def z177 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x087f60c300000000 0x043fb06180000000

def z178 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xd5801820c31e67e7 0xeac00c10618f33f3

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x35008000031c0001 0x1a804000018e0000

def z180 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfff87cf3e703ffff 0xfffc3e79f381ffff

def z181 : W := mkw 0x0066ff00010a2000 0x80337f8000851000 0x7d7fff00031e6001 0x3ebfff80018f3000

def z182 : W := mkw 0x0045805800000000 0x0022c02c00000000 0x2007801c00000000 0x1003c00e00000000

def z183 : W := mkw 0x012276000041c001 0x00913b000020e000 0x0000600000018000 0x000030000000c000

def z184 : W := mkw 0x2800000048000122 0x1400000024000091 0x00000000f8000026 0x800000007c000013

def z185 : W := mkw 0x117ffffbb7fbe88d 0x88bffffddbfdf446 0xfffffffffffff8ff 0xfffffffffffffc7f

def z186 : W := mkw 0x4081005c00240ac0 0x2040802e00120560 0x0000001c000000c0 0x0000000e00000060

def z187 : W := mkw 0x4000000400040240 0x2000000200020120 0xf580843c231e67e7 0xfac0421e118f33f3

def z188 : W := mkw 0x005480a800000000 0x002a405400000000 0x1078802c00000000 0x083c401600000000

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000871c38000000 0x1000438e1c000000

def z190 : W := mkw 0x20000002c0000130 0x1000000160000098 0x00000003c0000038 0x80000001e000001c

def z191 : W := mkw 0x20205802c1030130 0x10102c0160818098 0x40007803c0038038 0xa0003c01e001c01c

def z192 : W := mkw 0xe87fffffff0f3772 0xf43fffffff879bb9 0xffffffffff1fffff 0xffffffffff8fffff

def z193 : W := mkw 0x80dd80f806b01c80 0x406ec07c03580e40 0xbe7f80fc04e01800 0x5f3fc07e02700c00

def z194 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x307f9f3cf8000000 0x183fcf9e7c000000

def z195 : W := mkw 0x68000104480c2362 0xb4000082240611b1 0xa180873cf81c67e6 0xd0c0439e7c0e33f3

def z196 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x10781820c3000700 0x083c0c1061800380

def z197 : W := mkw 0x100100500060c88d 0x0800802800306446 0xaf8700d004e3f8ff 0x57c380680271fc7f

def z198 : W := mkw 0x40000904010e2240 0xa000048200871120 0xf5809f3c031e67c1 0x7ac04f9e018f33e0

def z199 : W := mkw 0xa13859a2c7dbf531 0xd09c2cd163edfa98 0xdff878e3c7ffff39 0xeffc3c71e3ffff9c

def z200 : W := mkw 0x4000000400040240 0x2000000200020120 0xf5809f3cfb1c07c1 0xfac04f9e7d8e03e0

def z201 : W := mkw 0xb03958f3e7231dbc 0x581cac79f3918ede 0xdef878f3e7039fff 0xef7c3c79f381cfff

def z202 : W := mkw 0x100000012000000c 0x0800000090000006 0x000000032000003e 0x800000019000001f

def z203 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xdc7f78e3c0000000 0xee3fbc71e0000000

def z204 : W := mkw 0x38032d51696ae9af 0x9c0196a8b4b574d7 0xef877fd3fce3f8ff 0xf7c3bfe9fe71fc7f

def z205 : W := mkw 0x80fdd0fa86b11c90 0x407ee87d43588e48 0x0a7f60c304e19818 0x053fb0618270cc0c

def z206 : W := mkw 0x003050a280000000 0x0018285140000000 0x10781820c0000000 0x083c0c1060000000

def z207 : W := mkw 0x11227f01214be00d 0x88913f8090a5f006 0x40007f032003e03e 0xa0003f819001f01f

def z208 : W := mkw 0x216eff0047dbe121 0x90b77f8023edf090 0xffffff20c7ffe721 0xffffff9063fff390

def z209 : W := mkw 0x696eff044fdfe363 0xb4b77f8227eff1b1 0xffffff3cffffe7e7 0xffffff9e7ffff3f3

def z210 : W := mkw 0x4000000400040240 0x2000000200020120 0x01800000031c07c1 0x00c00000018e03e0

def z211 : W := mkw 0x0128590007dbe001 0x80942c8003edf000 0x5f78780007ffe001 0x2fbc3c0003fff000

def z212 : W := mkw 0xe0b958fec7271ff0 0x705cac7f63938ff8 0xdef878ffc7039ff9 0xef7c3c7fe381cffc

def z213 : W := mkw 0x00237653b0000000 0x0011bb29d8000000 0xec077fd3f8000000 0xf603bfe9fc000000

def z214 : W := mkw 0xa03a7ca2c743d531 0x501d3e5163a1ea98 0xffff7ce3c7e3ff39 0xffffbe71e3f1ff9c

def z215 : W := mkw 0x0008000006000000 0x0004000003000000 0x1e78000007000001 0x0f3c000003800000

def z216 : W := mkw 0x004c800006900000 0x0026400003480000 0x10788000031c0000 0x083c4000018e0000

def z217 : W := mkw 0x100324512060c88d 0x0801922890306446 0x2107041020e060c6 0x1083820810703063

def z218 : W := mkw 0x7801005568240bee 0x3c00802ab41205f7 0x808000fff8001ffe 0xc040007ffc000fff

def z219 : W := mkw 0x0028580007030000 0x00142c0003818000 0x1078180003000000 0x083c0c0001800000

def z220 : W := mkw 0x100100512060c88d 0x0800802890306446 0x838000d324e3f8ff 0xc1c000699271fc7f

def z221 : W := mkw 0x017ffffbb7dbe001 0x80bffffddbedf000 0xff7fffffffffe001 0xffbffffffffff000

def z222 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x12f81820c7039f39 0x097c0c106381cf9c

def z223 : W := mkw 0x20227e03f1030130 0x10113f01f8818098 0x40007f03f8038038 0xa0003f81fc01c01c

def z224 : W := mkw 0x0100010000d8e001 0x80800080006c7000 0x0100000000fc6000 0x00800000007e3000

def z225 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xe5800410231e67e7 0xf2c00208118f33f3

def z226 : W := mkw 0x100224012040c00d 0x0801120090206006 0x6f07640324e3e03f 0xb783b2019271f01f

def z227 : W := mkw 0x4946a70408dce243 0xa4a35382046e7121 0x2107871c38fc60c6 0x1083c38e1c7e3063

def z228 : W := mkw 0x4800000408040242 0x2400000204020121 0x0000001c380000c6 0x0000000e1c000063

def z229 : W := mkw 0xe8fdd9fecfbf3ff2 0xf47eecff67df9ff9 0xffffffffffffffff 0xffffffffffffffff

def z230 : W := mkw 0x216eff02c7dbe131 0x90b77f8163edf098 0x7f7fff03c7ffe039 0xbfbfff81e3fff01c

def z231 : W := mkw 0x100000000060c88d 0x0800000000306446 0x0100000000e060c6 0x0080000000703063

def z232 : W := mkw 0x48000104080c2242 0xa400008204061121 0x01000000001c60c6 0x00800000000e3063

def z233 : W := mkw 0x6800000448040362 0x34000002240201b1 0x00800000000007e6 0x00400000000003f3

def z234 : W := mkw 0xc0d580fc00241ec0 0x606ac07e00120f60 0xbcff80fc00001fc0 0x5e7fc07e00000fe0

def z235 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff1027ffe0e7 0xffffff8813fff073

def z236 : W := mkw 0x20205802c1030130 0x10102c0160818098 0x00001800c0000000 0x00000c0060000000

def z237 : W := mkw 0x00c5805800b00880 0x0062c02c00580440 0x0007000000e00000 0x0003800000700000

def z238 : W := mkw 0x016fff5127dbe001 0x80b7ffa893edf000 0xff7fffd327ffe001 0xffbfffe993fff000

def z239 : W := mkw 0x004ea40006d0c001 0x0027520003686000 0x7f7fe40007ffe001 0x3fbff20003fff000

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0x10009b2cd8000000 0x08004d966c000000

def z241 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0x3f7f802c07fc0701 0x1fbfc01603fe0380

def z242 : W := mkw 0x20285802c7030130 0x10142c0163818098 0x5e787803c7038039 0xaf3c3c01e381c01c

def z243 : W := mkw 0x0146a70000d8e001 0x80a35380006c7000 0x6f07e70004ffe001 0x3783f380027ff000

def z244 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x3f7f9b0007fc0001 0x1fbfcd8003fe0000

def z245 : W := mkw 0x0001005000200880 0x0000802800100440 0xef8704d024e278e7 0xf7c3826812713c73

def z246 : W := mkw 0x0003245120000000 0x0001922890000000 0x2007041020000000 0x1003820810000000

def z247 : W := mkw 0x6877f6fff8040362 0x343bfb7ffc0201b1 0xfcfffffff80007e6 0xfe7ffffffc0003f3

def z248 : W := mkw 0x78000904496eebef 0xbc00048224b775f7 0xf7809f3cffffffff 0xfbc04f9e7fffffff

def z249 : W := mkw 0x0066f603b0000000 0x00337b01d8000000 0x7c7fff03f8000000 0xbe3fff81fc000000

def z250 : W := mkw 0x100000000060c88d 0x0800000000306446 0x0380000004e3f8ff 0x01c000000271fc7f

def z251 : W := mkw 0x28000900490a2122 0x9400048024851091 0x75009f00fb1e6027 0xba804f807d8f3013

def z252 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0xb5f8803c031c07c1 0x5afc401e018e03e0

def z253 : W := mkw 0x01227f00014be001 0x80913f8000a5f000 0x7500ff00031fe001 0x3a807f80018ff000

def z254 : W := mkw 0x016eff00079b2000 0x80b77f8003cd9000 0x7c7fff00031c0000 0x3e3fff80018e0000

def z255 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x75009f2cdb1e6701 0x3a804f966d8f3380

def z256 : W := mkw 0x684c89044f9e2362 0xb426448227cf11b1 0xffff9f3cfffe67e7 0xffffcf9e7fff33f3

def z257 : W := mkw 0xe81009a6c90e3772 0xf40804d364871bb9 0xf5809ffffb1e7fff 0xfac04ffffd8f3fff

def z258 : W := mkw 0x0000080001020000 0x0000040000810000 0x5400180003020001 0x2a000c0001810000

def z259 : W := mkw 0x0003245120000000 0x0001922890000000 0xfc07fffff8000000 0xfe03fffffc000000

def z260 : W := mkw 0x101324fbb060c88d 0x0809927dd8306446 0xef8764fffce3f8ff 0xf7c3b27ffe71fc7f

def z261 : W := mkw 0x0003245120000000 0x0001922890000000 0x080760c300000000 0x0403b06180000000

def z262 : W := mkw 0x0000000000200880 0x0000000000100440 0x0380000004e018c1 0x01c0000002700c60

def z263 : W := mkw 0xc0dfa4fc06f4dec1 0x606fd27e037a6f60 0xffffe4fc07ffffc1 0x7ffff27e03ffffe0

def z264 : W := mkw 0x40c5805c00b40ac0 0x2062c02e005a0560 0xaf8780dc04fc18c1 0x57c3c06e027e0c60

def z265 : W := mkw 0xc0cc800406b41ec0 0x60664002035a0f60 0x3fff800007fc1fc1 0x1fffc00003fe0fe0

def z266 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400041020000000 0xf200020810000000

def z267 : W := mkw 0x005580fbb0000000 0x002ac07dd8000000 0xbc7f80fff8000000 0xde3fc07ffc000000

def z268 : W := mkw 0x116eff0127dbe00d 0x88b77f8093edf006 0x7f7fff0327ffe03f 0xbfbfff8193fff01f

def z269 : W := mkw 0xe89100fc48241fe2 0x7448807e24120ff1 0x808000fcf8001fe6 0xc040007e7c000ff3

def z270 : W := mkw 0x001100f800000000 0x0008807c00000000 0x800000fc00000000 0x4000007e00000000

def z271 : W := mkw 0x6800000448040362 0x34000002240201b1 0xe580043cf80267e7 0xf2c0021e7c0133f3

def z272 : W := mkw 0xa13a7fa2c74bf531 0xd09d3fd163a5fa98 0xdef87fe3c703ff39 0xef7c3ff1e381ff9c

def z273 : W := mkw 0xa17effa2c7dbf531 0xd0bf7fd163edfa98 0x7f7fff20c7ffe701 0x3fbfff9063fff380

def z274 : W := mkw 0xc1dd89fc07fffec1 0xe0eec4fe03ffff60 0xbfff80fc07ffffc1 0x5fffc07e03ffffe0

def z275 : W := mkw 0xc0dfa6fd36b41ec0 0x606fd37e9b5a0f60 0xbfff87fc3ffc1fc1 0x5fffc3fe1ffe0fe0

def z276 : W := mkw 0x016cd20006910000 0x00b6690003488000 0x0078000000000000 0x003c000000000000

def z277 : W := mkw 0x017ff6fbb6d1c001 0x00bffb7ddb68e000 0xfe7ffffffce18000 0xff3ffffffe70c000

def z278 : W := mkw 0xe89109fc492e3fe2 0xf44884fe24971ff1 0xf5809ffcfb1e7fe7 0xfac04ffe7d8f3ff3

def z279 : W := mkw 0x78000904496eebef 0xbc00048224b775f7 0x0380000007ffffff 0x01c0000003ffffff

def z280 : W := mkw 0xb01100f3e0201dbc 0x58088079f0100ede 0x808000f3e0001ffe 0xc0400079f0000fff

def z281 : W := mkw 0x0076f6abb0000000 0x003b7b55d8000000 0x5078ff2ff8000000 0xa83c7f97fc000000

def z282 : W := mkw 0x014ea70006d8e001 0x80a75380036c7000 0x3f7f870007fc6001 0x1fbfc38003fe3000

def z283 : W := mkw 0xc0fdd0fe86b41ec0 0x607ee87f435a0f60 0xfffff8ffc7fc1fc1 0xfffffc7fe3fe0fe0

def z284 : W := mkw 0x000224000040c001 0x0001120000206000 0x0a07600004e18000 0x0503b0000270c000

def z285 : W := mkw 0x0003245120200880 0x0001922890100440 0xef8764d324e018c1 0xf7c3b26992700c60

def z286 : W := mkw 0x10237653b060c88d 0x0811bb29d8306446 0xef877fd3fce3f8ff 0xf7c3bfe9fe71fc7f

def z287 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x90f818e3c3001f38 0xc87c0c71e1800f9c

def z288 : W := mkw 0x38022d01694ae12f 0x9c011680b4a57097 0x40007f03f803e03e 0xa0003f81fc01f01f

def z289 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfe7ffffffce19818 0xff3ffffffe70cc0c

def z290 : W := mkw 0xd0dfa4fd26f4decd 0x686fd27e937a6f66 0xbfff84fc27fc7fc7 0x5fffc27e13fe3fe3

def z291 : W := mkw 0xa01808a047021520 0x500c045023810a90 0xdef818e0c7021f21 0xef7c0c7063810f90

def z292 : W := mkw 0x016fff5937dbe001 0x80b7ffac9bedf000 0x7f7fff1c3fffe001 0x3fbfff8e1ffff000

def z293 : W := mkw 0x016ef70006d9e001 0x80b77b80036cf000 0x2b7fe70004fde000 0x15bff380027ef000

def z294 : W := mkw 0x0166f70000d8e001 0x80b37b80006c7000 0x7d7fff0000fc6000 0x3ebfff80007e3000

def z295 : W := mkw 0x01000900014be001 0x8080048000a5f000 0x000000000003e000 0x000000000001f000

def z296 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0xb58080fc031c1fc1 0x5ac0407e018e0fe0

def z297 : W := mkw 0x0003245120000000 0x0001922890000000 0xee8764d324039839 0xf743b2699201cc1c

def z298 : W := mkw 0xa17cdba2c79b3530 0xd0be6dd163cd9a98 0xdef8fbe3c71f9f39 0xef7c7df1e38fcf9c

def z299 : W := mkw 0x0044800000000000 0x0022400000000000 0x3c7f800000000000 0x1e3fc00000000000

def z300 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z301 : W := mkw 0x48000104080c2242 0xa400008204061121 0x0000830c181c0000 0x000041860c0e0000

def z302 : W := mkw 0x017ffffbb7dbe001 0x80bffffddbedf000 0x7f7fffc307ffe001 0x3fbfffe183fff000

def z303 : W := mkw 0xa03058a2c1031530 0x50182c5160818a98 0xc08078e3c0039f38 0xe0403c71e001cf9c

def z304 : W := mkw 0x00227603b0000000 0x00113b01d8000000 0x0000600300000000 0x0000300180000000

def z305 : W := mkw 0x0076f6aa90000000 0x003b7b5548000000 0x7c7fff2cd8000000 0x3e3fff966c000000

def z306 : W := mkw 0x100224012040c00d 0x0801120090206006 0xce8064c32403f83f 0xe74032619201fc1f

def z307 : W := mkw 0xa07efea2c7031530 0x503f7f5163818a98 0xfeffffe3c7039f39 0xff7ffff1e381cf9c

def z308 : W := mkw 0x0001005930000000 0x0000802c98000000 0x0000001c38000000 0x0000000e1c000000

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z310 : W := mkw 0xb03858a2c763ddbd 0x581c2c5163b1eede 0xdff878e3c7e3ffff 0xeffc3c71e3f1ffff

def z311 : W := mkw 0x100000000060c88d 0x0800000000306446 0xe780041024e3f8ff 0xf3c002081271fc7f

def z312 : W := mkw 0x68010954492e2be2 0xb40084aa249715f1 0xff879ffcfffe7fe7 0xffc3cffe7fff3ff3

def z313 : W := mkw 0x20205802c1030130 0x10102c0160818098 0xd4807823c3038739 0xea403c11e181c39c

def z314 : W := mkw 0x10227603b040c00d 0x08113b01d8206006 0x40007f03f803e03e 0xa0003f81fc01f01f

def z315 : W := mkw 0x0064d20000000000 0x0032690000000000 0x10789b0000000000 0x083c4d8000000000

def z316 : W := mkw 0x6847af5d790e2362 0xb423d7aebc8711b1 0xf5879f3cfb1e67e7 0xfac3cf9e7d8f33f3

def z317 : W := mkw 0xa03a7ea3f7031530 0x501d3f51fb818a98 0xdef87fe3ff039f39 0xef7c3ff1ff81cf9c

def z318 : W := mkw 0x003050a280000000 0x0018285140000000 0xdef878e3c4039839 0xef7c3c71e201cc1c

def z319 : W := mkw 0x00000900010a2000 0x8000048000851000 0xf5809f10231e60e7 0xfac04f88118f3073

def z320 : W := mkw 0x0057a6fbb0000000 0x002bd37dd8000000 0xa00787fff8000000 0xd003c3fffc000000

def z321 : W := mkw 0x017ffffbb79b2000 0x80bffffddbcd9000 0xfc7ffffffb1c0000 0xfe3ffffffd8e0000

def z322 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x887f60fff8000000 0xc43fb07ffc000000

def z323 : W := mkw 0x58032555286ceacf 0xac0192aa94367567 0x2107871c38fc60c6 0x1083c38e1c7e3063

def z324 : W := mkw 0x005580f800200880 0x002ac07c00100440 0xbfff80fc04e018c1 0x5fffc07e02700c60

def z325 : W := mkw 0xc1ffffffb7fffec1 0xe0ffffffdbffff60 0xffffffffffffffc1 0xffffffffffffffe0

def z326 : W := mkw 0x001324fbb0000000 0x0009927dd8000000 0xec0764fff8000000 0xf603b27ffc000000

def z327 : W := mkw 0xb01324f3e060ddbd 0x58099279f0306ede 0xef8764f3e4e3ffff 0xf7c3b279f271ffff

def z328 : W := mkw 0x80dd80f806b01c80 0x406ec07c03580e40 0xafff00d004e018c1 0x57ff806802700c60

def z329 : W := mkw 0xe81000a6c8041772 0x7408005364020bb9 0x808000fff8001ffe 0xc040007ffc000fff

def z330 : W := mkw 0x016efe0007d3c001 0x00b77f0003e9e000 0x5e7f780007e38001 0x2f3fbc0003f1c000

def z331 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x61009f1cf81e60e6 0xb0804f8e7c0f3073

def z332 : W := mkw 0x28000900490a2122 0x9400048024851091 0xd4801f20fb026727 0xea400f907d813393

def z333 : W := mkw 0x100000000020088c 0x0800000000100446 0x00800000000018fe 0x0040000000000c7f

def z334 : W := mkw 0x100324512060c88d 0x0801922890306446 0x2387041024e3f8ff 0x11c382081271fc7f

def z335 : W := mkw 0xa03958f2c7231db0 0x501cac7963918ed8 0xffff78f3c7e39ff9 0xffffbc79e3f1cffc

def z336 : W := mkw 0xa03850a2c6011530 0x501c285163008a98 0x8af860e3c4019f38 0xc57c3071e200cf9c

def z337 : W := mkw 0x807ff6fbb6011410 0x403ffb7ddb008a08 0xfe7ffffffc019818 0xff3ffffffe00cc0c

def z338 : W := mkw 0xd0dd80fc06f4decd 0x686ec07e037a6f66 0xbfff80fc07ffffff 0x5fffc07e03ffffff

def z339 : W := mkw 0x2000000040000120 0x1000000020000090 0x80800020c0000720 0xc040001060000390

def z340 : W := mkw 0x803850a286011410 0x401c285143008a08 0xcef860c304039839 0xe77c30618201cc1c

def z341 : W := mkw 0x104fa45126f0c88d 0x0827d22893786446 0xffffe4d327fff8ff 0xfffff26993fffc7f

def z342 : W := mkw 0x2077fefbf1020120 0x103bff7df8810090 0xfcfffffffb020721 0xfe7ffffffd810390

def z343 : W := mkw 0x101100fbb020088c 0x0808807dd8100446 0x808000fff80018fe 0xc040007ffc000c7f

def z344 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x5e78fb00071f8001 0x2f3c7d80038fc000

def z345 : W := mkw 0x00000900010a2000 0x8000048000851000 0x40001f0000026000 0x20000f8000013000

def z346 : W := mkw 0x017cdbaa979b2000 0x80be6dd54bcd9000 0x10789b2cdb1c0000 0x083c4d966d8e0000

def z347 : W := mkw 0xc0fdd8fc07b71ec0 0x607eec7e03db8f60 0xfffff8fc07ff9fc1 0x7ffffc7e03ffcfe0

def z348 : W := mkw 0x0046a60000000000 0x0023530000000000 0x2007870000000000 0x1003c38000000000

def z349 : W := mkw 0xe8dd80fc4eb41fe2 0x746ec07e275a0ff1 0xbfff80fcfffc1fe7 0xdfffc07e7ffe0ff3

def z350 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x75789f00031e6001 0x3abc4f80018f3000

def z351 : W := mkw 0x90dfa4f926f0dc8d 0x486fd27c93786e46 0x0a7f60c304e19818 0x053fb0618270cc0c

def z352 : W := mkw 0x28000900490a2122 0x9400048024851091 0xe5801f10f80260e7 0xf2c00f887c013073

def z353 : W := mkw 0x100324512060c88d 0x0801922890306446 0x4a0764c324e3f83e 0xa503b2619271fc1f

def z354 : W := mkw 0x0066f60000000000 0x00337b0000000000 0x087f600000000000 0x043fb00000000000

def z355 : W := mkw 0x001000a280000000 0x0008005140000000 0x800000e3c0000000 0xc0000071e0000000

def z356 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfefffffffc039839 0xff7ffffffe01cc1c

def z357 : W := mkw 0x004d805006b00880 0x0026c02803580440 0xbfff80d007fc18c1 0x5fffc06803fe0c60

def z358 : W := mkw 0x803850a286011410 0x401c285143008a08 0xde7878e3c4019818 0xef3c3c71e200cc0c

def z359 : W := mkw 0x0144830000982000 0x80a24180004c1000 0x00008300001c0000 0x00004180000e0000

def z360 : W := mkw 0x000000000040c001 0x0000000000206000 0x0300000004e3e001 0x018000000271f000

def z361 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x0af860c307039f39 0x057c30618381cf9c

def z362 : W := mkw 0x6800000448040362 0x34000002240201b1 0x8080003cf80007e6 0xc040001e7c0003f3

def z363 : W := mkw 0x78022d05694ee36f 0xbc011682b4a771b7 0xf580ff3ffb1fe7ff 0xfac07f9ffd8ff3ff

def z364 : W := mkw 0x000224000040c001 0x0001120000206000 0x2107040000e06000 0x1083820000703000

def z365 : W := mkw 0x016fff5007fbe881 0x80b7ffa803fdf440 0xffffffd007fff8c1 0x7fffffe803fffc60

def z366 : W := mkw 0x203058a2c1020120 0x10182c5160810090 0xdcf878e3c3020721 0xee7c3c71e1810390

def z367 : W := mkw 0x685589fc490e2362 0xb42ac4fe248711b1 0xfdff9ffcfb1e67e7 0xfeffcffe7d8f33f3

def z368 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfdfffffff80260e7 0xfefffffffc013073

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x9480002003000701 0x4a40001001800380

def z370 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xbc7fe0ff00000000 0x5e3ff07f80000000

def z371 : W := mkw 0x40d580fc00b40ac0 0x206ac07e005a0560 0xbd7f80fc00fc00c0 0x5ebfc07e007e0060

def z372 : W := mkw 0x1077f6fbb020088c 0x083bfb7dd8100446 0xfcfffffff80018fe 0xfe7ffffffc000c7f

def z373 : W := mkw 0xf8dfadfd6ffeffef 0xfc6fd6feb7ff7ff7 0xffffffffffffffff 0xffffffffffffffff

def z374 : W := mkw 0x100224012040c00d 0x0801120090206006 0x0000600300018018 0x000030018000c00c

def z375 : W := mkw 0x0020520290000000 0x0010290148000000 0x00001b00d8000000 0x00000d806c000000

def z376 : W := mkw 0x0001005000200880 0x0000802800100440 0x2107001000e000c0 0x1083800800700060

def z377 : W := mkw 0xa0fdd8fac7b31db0 0x507eec7d63d98ed8 0xdeff78e3c7e39f39 0xef7fbc71e3f1cf9c

def z378 : W := mkw 0x000324512040c001 0x0001922890206000 0xef0764d324e3e001 0xf783b2699271f000

def z379 : W := mkw 0x803850a286011410 0x401c285143008a08 0x0078000000000000 0x003c000000000000

def z380 : W := mkw 0x681100fff8040362 0x3408807ffc0201b1 0x808000fff80007e6 0xc040007ffc0003f3

def z381 : W := mkw 0x803858a287031410 0x401c2c5143818a08 0x5e7878c307039819 0x2f3c3c618381cc0c

def z382 : W := mkw 0xc188090407fffec1 0xe0c4048203ffff60 0x0380000007ffffc1 0x01c0000003ffffe0

def z383 : W := mkw 0x4847a75d380c2242 0xa423d3ae9c061121 0x2107871c381c60c6 0x1083c38e1c0e3063

def z384 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x90f880fc031c1fc0 0x487c407e018e0fe0

def z385 : W := mkw 0x6874dbaed90e2362 0xb43a6dd76c8711b1 0x10789b2cdb1c0700 0x083c4d966d8e0380

def z386 : W := mkw 0x100324512060c88d 0x0801922890306446 0xed0764d320e060c6 0xf683b26990703063

def z387 : W := mkw 0x2028580047030120 0x10142c0023818090 0xdef87820c7038721 0xef7c3c106381c390

def z388 : W := mkw 0xc0f7f6ffb0241ec0 0x607bfb7fd8120f60 0xfcfffffff8001fc0 0xfe7ffffffc000fe0

def z389 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x1a7ffb0007fd8000 0x0d3ffd8003fec000

def z390 : W := mkw 0xe83859a6cf0f3772 0xf41c2cd367879bb9 0xdef8fbefdf1f9f39 0xef7c7df7ef8fcf9c

def z391 : W := mkw 0x00000003b0000000 0x00000001d8000000 0x00000003f8000000 0x80000001fc000000

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x808000c300001838 0xc040006180000c1c

def z393 : W := mkw 0x007ff6fbb6900000 0x003ffb7ddb480000 0xff7ffffffffc0001 0xffbffffffffe0000

def z394 : W := mkw 0x803850a286011410 0x401c285143008a08 0x9ef860e307019f19 0x4f7c30718380cf8c

def z395 : W := mkw 0x801000a000001400 0x4008005000000a00 0x808000e000001f00 0x4040007000000f80

def z396 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffffc307fff839 0xffffffe183fffc1c

def z397 : W := mkw 0x68205906c90f2372 0xb4102c83648791b9 0xf580ff3ffb1fe7ff 0xfac07f9ffd8ff3ff

def z398 : W := mkw 0x404c800406940240 0x20264002034a0120 0xbfff803c07fc07c1 0x5fffc01e03fe03e0

def z399 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x287fe7df38000000 0x143ff3ef9c000000

def z400 : W := mkw 0xc0fdd0fe86b51ed0 0x607ee87f435a8f68 0xbfffe0ff07fd9fd9 0x5ffff07f83fecfec

def z401 : W := mkw 0x100224012040c00d 0x0801120090206006 0xe58064132003e0ff 0xf2c032099001f07f

def z402 : W := mkw 0x006ef60006900000 0x00377b0003480000 0x7f7fff0007fc0001 0x3fbfff8003fe0000

def z403 : W := mkw 0x805c80a006901400 0x402e405003480a00 0xbfff80e007fc1f01 0x5fffc07003fe0f80

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a0060c304019818 0x050030618200cc0c

def z405 : W := mkw 0x90dfa4f926f0dc8d 0x486fd27c93786e46 0xefff64d324e3f8ff 0xf7ffb2699271fc7f

def z406 : W := mkw 0x48000104080c2242 0xa400008204061121 0xf5009f3cf81c60c6 0xfa804f9e7c0e3063

def z407 : W := mkw 0x6800000448040362 0x34000002240201b1 0xf4809f3cf80007e6 0xfa404f9e7c0003f3

def z408 : W := mkw 0x100324512060c88d 0x0801922890306446 0x6f0764c304e3f819 0x3783b2618271fc0c

def z409 : W := mkw 0x803858a007031400 0x401c2c5003818a00 0xdef878e007039f01 0x6f7c3c700381cf80

def z410 : W := mkw 0xe8dc89ac4f9e3762 0xf46e44d627cf1bb1 0x10789b2cdb1c0700 0x083c4d966d8e0380

def z411 : W := mkw 0xa01808a2c7031530 0x500c045163818a98 0x828000e3c7039f39 0xc1400071e381cf9c

def z412 : W := mkw 0xc0dfa4fd26b41ec0 0x606fd27e935a0f60 0xffffe4ff27fc1fc1 0xfffff27f93fe0fe0

def z413 : W := mkw 0x006efe0007030000 0x00377f0003818000 0x7e7fff0007038001 0x3f3fff800381c000

def z414 : W := mkw 0xe0fdd8fec7b71ff0 0x707eec7f63db8ff8 0xbfff98fcc7fc1fc1 0x5fffcc7e63fe0fe0

def z415 : W := mkw 0x20205802c1030130 0x10102c0160818098 0xce8078c3c4039839 0xe7403c61e201cc1c

def z416 : W := mkw 0x100324512060c88d 0x0801922890306446 0x2b0764d324e1f8de 0x1583b2699270fc6f

def z417 : W := mkw 0x003858a287030000 0x001c2c5143818000 0xde7878e3c7038001 0xef3c3c71e381c000

def z418 : W := mkw 0xa028580047031530 0x50142c0023818a98 0x5ef8780007039f39 0x2f7c3c000381cf9c

def z419 : W := mkw 0x805d80f806001400 0x402ec07c03000a00 0xbeff80fc07001f01 0x5f7fc07e03800f80

def z420 : W := mkw 0x000224000040c001 0x0001120000206000 0xef8764c304e3f839 0xf7c3b2618271fc1c

def z421 : W := mkw 0x100324512060c88d 0x0801922890306446 0x6f07641024e3e0c7 0x3783b2081271f063

def z422 : W := mkw 0x003376fbb0000000 0x0019bb7dd8000000 0xc0007ffff8000000 0xe0003ffffc000000

def z423 : W := mkw 0xe83859a6cf0f3772 0xf41c2cd367879bb9 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z424 : W := mkw 0xe0fcd8aec7971770 0x707e6c5763cb8bb8 0xdef8f8efc71f9f39 0xef7c7c77e38fcf9c

def z425 : W := mkw 0x2000080041020120 0x1000040020810090 0xde8078e3c7039f39 0xef403c71e381cf9c

def z426 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x487f7fc3f8000000 0xa43fbfe1fc000000

def z427 : W := mkw 0x48000104080c2242 0xa400008204061121 0xb580873c3b1c67c7 0x5ac0439e1d8e33e3

def z428 : W := mkw 0x0077f6fbb040c001 0x003bfb7dd8206000 0xff7ffffffce3e001 0xffbffffffe71f000

def z429 : W := mkw 0x0075d0fa80000000 0x003ae87d40000000 0xfc7ff8ffc0000000 0xfe3ffc7fe0000000

def z430 : W := mkw 0xc0fcd2ae96941640 0x607e69574b4a0b20 0x10789b2cdb1c0700 0x083c4d966d8e0380

def z431 : W := mkw 0x002a7c000743c001 0x00153e0003a1e000 0x7f7f7c0007e3e001 0x3fbfbe0003f1f000

def z432 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0x0a7f60c304e19818 0x053fb0618270cc0c

def z433 : W := mkw 0xa07dd8fac7031530 0x503eec7d63818a98 0xfefff8ffc7039f39 0xff7ffc7fe381cf9c

def z434 : W := mkw 0x2000080041020120 0x1000040020810090 0x10001820c3000700 0x08000c1061800380

def z435 : W := mkw 0x30237c53e163c9bd 0x1811be29f0b1e4de 0xef877cd3e4e3f8ff 0xf7c3be69f271fc7f

def z436 : W := mkw 0xa03958fbf7031530 0x501cac7dfb818a98 0xdef878ffff039f39 0xef7c3c7fff81cf9c

def z437 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x8aff00fc04e01fc0 0x457f807e02700fe0

def z438 : W := mkw 0x003050a280000000 0x0018285140000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z439 : W := mkw 0x0047a65930000000 0x0023d32c98000000 0xec07e7df38000000 0xf603f3ef9c000000

def z440 : W := mkw 0x80dd80f806b01c80 0x406ec07c03580e40 0x9eff00e007e01f01 0x4f7f807003f00f80

def z441 : W := mkw 0xa83859a2cf0b3532 0xd41c2cd167859a99 0xdef87fe3ff03ff3f 0xef7c3ff1ff81ff9f

def z442 : W := mkw 0xe97effa6cfdff773 0xf4bf7fd367effbb9 0xffffffffffffffff 0xffffffffffffffff

def z443 : W := mkw 0x30032c516162c9ad 0x18019628b0b164d6 0xff877cf3e7e3ffff 0xffc3be79f3f1ffff

def z444 : W := mkw 0x6874dbaed90e2362 0xb43a6dd76c8711b1 0xf5f89f3cfb1e67e7 0xfafc4f9e7d8f33f3

def z445 : W := mkw 0x796fff556fffebef 0xbcb7ffaab7fff5f7 0xffffffffffffffff 0xffffffffffffffff

def z446 : W := mkw 0x0000010000082000 0x8000008000041000 0x21008700001c6000 0x10804380000e3000

def z447 : W := mkw 0xc1dfa7fc06fcfec1 0xe0efd3fe037e7f60 0xbfff87fc07fc7fc1 0x5fffc3fe03fe3fe0

def z448 : W := mkw 0x416eff0407dfe241 0xa0b77f8203eff120 0xffffff3c07ffe7c1 0x7fffff9e03fff3e0

def z449 : W := mkw 0xa03859a2c70b3530 0xd01c2cd163859a98 0xfff8ffe3c71fff39 0xfffc7ff1e38fff9c

def z450 : W := mkw 0xd088000406f4decd 0x68440002037a6f66 0x0380000007ffffff 0x01c0000003ffffff

def z451 : W := mkw 0x100324512060c88d 0x0801922890306446 0x6107641320e3e0fe 0xb083b2099071f07f

def z452 : W := mkw 0x00000900010a2000 0x8000048000851000 0xf5009f3cfb1e6001 0xfa804f9e7d8f3000

def z453 : W := mkw 0xc1feffac07dff641 0xe0ff7fd603effb20 0x7f7fff2c07ffe701 0x3fbfff9603fff380

def z454 : W := mkw 0x00000900010a2000 0x8000048000851000 0x01000000031e6001 0x00800000018f3000

def z455 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff3cffffe001 0xffbfff9e7ffff000

def z456 : W := mkw 0x0028580007030000 0x00142c0003818000 0xdef878c307039839 0xef7c3c618381cc1c

def z457 : W := mkw 0xd0dd80fd26b41ecc 0x686ec07e935a0f66 0xbfff80ff27fc1fff 0xdfffc07f93fe0fff

def z458 : W := mkw 0x80dd80f806b01c80 0x406ec07c03580e40 0x3f7f80c007fc1801 0x1fbfc06003fe0c00

def z459 : W := mkw 0x0800010008082002 0x8400008004041001 0x0000070038006006 0x000003801c003003

def z460 : W := mkw 0x681109fff90e2362 0xb40884fffc8711b1 0xf5809ffffb1e67e7 0xfac04ffffd8f33f3

def z461 : W := mkw 0x100324512060c88d 0x0801922890306446 0x0b8760c304e3f8ff 0x05c3b0618271fc7f

def z462 : W := mkw 0x4001005400240ac0 0x2000802a00120560 0xbf8780fc07fc1fc1 0x5fc3c07e03fe0fe0

def z463 : W := mkw 0xe03858a6c7071770 0x701c2c5363838bb8 0xfff8f8ffc71f9ff9 0xfffc7c7fe38fcffc

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x0280000004039839 0x014000000201cc1c

def z465 : W := mkw 0x1057a4f92060c88d 0x082bd27c90306446 0xffffe4ff24e3f8ff 0xfffff27f9271fc7f

def z466 : W := mkw 0x0077fffbb10a2000 0x803bfffdd8851000 0xfd7ffffffb1e6001 0xfebffffffd8f3000

def z467 : W := mkw 0x80fff6fbb6b01c80 0x407ffb7ddb580e40 0xfe7ffffffce01800 0xff3ffffffe700c00

def z468 : W := mkw 0x100000000060c88d 0x0800000000306446 0x0200000004e19818 0x010000000270cc0c

def z469 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffffe0ff07ff9ff9 0xfffff07f83ffcffc

def z470 : W := mkw 0x0166ff00014be001 0x80b37f8000a5f000 0x7c7fff000003e000 0x3e3fff800001f000

def z471 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x7c7fffc300000000 0x3e3fffe180000000

def z472 : W := mkw 0x102b7c512763c88d 0x0815be2893b1e446 0xffff7cd327e3f8ff 0xffffbe6993f1fc7f

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e8000c004001801 0x4740006002000c00

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000600300038038 0xa00030018001c01c

def z475 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x8180003cfb1e67e7 0xc0c0001e7d8f33f3

def z476 : W := mkw 0x2000080041020120 0x1000040020810090 0x40001800c0020020 0xa0000c0060010010

def z477 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc0060c300000000 0xe600306180000000

def z478 : W := mkw 0x405580fc00040240 0x202ac07e00020120 0xbdff80fc031c07c1 0x5effc07e018e03e0

def z479 : W := mkw 0x696eff044fdfe363 0xb4b77f8227eff1b1 0x7fffff0007ffe7e7 0x3fffff8003fff3f3

def z480 : W := mkw 0x809100f800201c80 0x4048807c00100e40 0x000000c000001800 0x0000006000000c00

def z481 : W := mkw 0x01227f00014be001 0x80913f8000a5f000 0x6f077f0004e3e001 0x3783bf800271f000

def z482 : W := mkw 0x0047a65930000000 0x0023d32c98000000 0xf4079f3cf8000000 0xfa03cf9e7c000000

def z483 : W := mkw 0x801000a280001410 0x4008005140000a08 0x000000c300001818 0x0000006180000c0c

def z484 : W := mkw 0xe0dd88fc47b61fe0 0x706ec47e23db0ff0 0xffff98fcc7fe1fe1 0xffffcc7e63ff0ff0

def z485 : W := mkw 0x1067f6512060c88d 0x0833fb2890306446 0xffffffd324e3f8ff 0xffffffe99271fc7f

def z486 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x00000000031c0700 0x00000000018e0380

def z487 : W := mkw 0x40f7f6ffb0b40ac0 0x207bfb7fd85a0560 0xfd7ffffff8fc00c0 0xfebffffffc7e0060

def z488 : W := mkw 0x017ff6fbb6d1c001 0x00bffb7ddb68e000 0x0a7f60c304e18000 0x053fb0618270c000

def z489 : W := mkw 0x2000080041020120 0x1000040020810090 0x0080000003020721 0x0040000001810390

def z490 : W := mkw 0xe80809044f0f3772 0xf404048227879bb9 0xf7809f3cff1fffff 0xfbc04f9e7f8fffff

def z491 : W := mkw 0x100324512020088c 0x0801922890100446 0xec8764d3200018fe 0xf643b26990000c7f

def z492 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x0bff00c007fc1fc1 0x05ff806003fe0fe0

def z493 : W := mkw 0x0002260130000000 0x0001130098000000 0x0000070038000000 0x000003801c000000

def z494 : W := mkw 0x80fff6fbb6b01c80 0x407ffb7ddb580e40 0x0a7f60c304e01800 0x053fb06182700c00

def z495 : W := mkw 0x014c890007dbe001 0x80a6448003edf000 0x3f7f800007ffe001 0x1fbfc00003fff000

def z496 : W := mkw 0x0077f6fbb0200880 0x003bfb7dd8100440 0xfffffffffce018c1 0xfffffffffe700c60

def z497 : W := mkw 0x2077fefbf1030130 0x103bff7df8818098 0xfc7ffffff8038038 0xfe3ffffffc01c01c

def z498 : W := mkw 0x014eaf0007dbe001 0x80a7578003edf000 0x2307870007ffe001 0x1183c38003fff000

def z499 : W := mkw 0xc09900fc06b41ec0 0x604c807e035a0f60 0x838000fc07fc1fc1 0x41c0007e03fe0fe0

def z500 : W := mkw 0x001000aa90000000 0x0008005548000000 0x0000002cd8000000 0x000000166c000000

def z501 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x41801f00fb1e67e7 0xa0c00f807d8f33f3

def z502 : W := mkw 0x003374f3a0000000 0x0019ba79d0000000 0xfc7f7cf3e0000000 0xfe3fbe79f0000000

def z503 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x5078ff00031fe000 0x283c7f80018ff000

def z504 : W := mkw 0xc080000400241ec0 0x6040000200120f60 0x0080000000001fc0 0x0040000000000fe0

def z505 : W := mkw 0x012a7f0007dbe001 0x80953f8003edf000 0x43007f0007ffe001 0x21803f8003fff000

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x80800010200000e6 0xc040000810000073

def z507 : W := mkw 0x58032555286ceacf 0xac0192aa94367567 0xef87e7df3cfff8ff 0xf7c3f3ef9e7ffc7f

def z508 : W := mkw 0xe8dd89fc4fbe3fe2 0xf46ec4fe27df1ff1 0xbfff80fc07fe7fe7 0x5fffc07e03ff3ff3

def z509 : W := mkw 0x801900f006201c80 0x400c807803100e40 0xbfff00f007e01fc1 0x5fff807803f00fe0

def z510 : W := mkw 0x00285900070b2000 0x80142c8003859000 0x7f78ff00071fe001 0x3fbc7f80038ff000

def z511 : W := mkw 0x6000080441060360 0x30000402208301b0 0xf580983cc31e07e1 0xfac04c1e618f03f0

def z512 : W := mkw 0x780324556864cbef 0x3c01922ab43265f7 0xef8764fffce3ffff 0xf7c3b27ffe71ffff

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0xa5800010000000c1 0x52c0000800000060

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0xd4001820c0000000 0xea000c1060000000

def z515 : W := mkw 0x30227c03e143c13d 0x18113e01f0a1e09e 0x40007c03e003e03e 0xa0003e01f001f01f

def z516 : W := mkw 0x78032d55696eebef 0xbc0196aab4b775f7 0xf5879f3cfbfe67e7 0xfac3cf9e7dff33f3

def z517 : W := mkw 0x0067f65bb0000000 0x0033fb2dd8000000 0x6007ff1ff8000000 0xb003ff8ffc000000

def z518 : W := mkw 0x8008000006011410 0x4004000003008a08 0x0200000004019818 0x010000000200cc0c

def z519 : W := mkw 0xc0fff6fc06b41ec0 0x607ffb7e035a0f60 0xfffffffc07fc1fc1 0x7ffffffe03fe0fe0

def z520 : W := mkw 0x203058a2c1030130 0x10182c5160818098 0xdc7878e3c0038038 0xee3c3c71e001c01c

def z521 : W := mkw 0x81fffff807fbfc81 0xc0fffffc03fdfe40 0x7f7fffc007fff801 0x3fbfffe003fffc00

def z522 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xd4f81820c3020721 0xea7c0c1061810390

def z523 : W := mkw 0x0001005000200880 0x0000802800100440 0x0a0700c004e01800 0x0503806002700c00

def z524 : W := mkw 0x1147a75120f8e88d 0x88a3d3a8907c7446 0x2107871020fc60c6 0x1083c388107e3063

def z525 : W := mkw 0xc1fddbfc07bf3ec0 0xe0feedfe03df9f60 0xbfff9bfc07fc1fc1 0x5fffcdfe03fe0fe0

def z526 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0xaf8700fc04e01fc1 0x57c3807e02700fe0

def z527 : W := mkw 0x116eff0007fbe88d 0x88b77f8003fdf446 0x7fffff0007fff8ff 0x3fffff8003fffc7f

def z528 : W := mkw 0x0146a60000d0c001 0x00a3530000686000 0x0007000000e00000 0x0003800000700000

def z529 : W := mkw 0xe0dd80fec6b41ff0 0x706ec07f635a0ff8 0xbfff80ffc7fc1ff9 0xdfffc07fe3fe0ffc

def z530 : W := mkw 0x0008000006900000 0x0004000003480000 0x0300000007fc0001 0x0180000003fe0000

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0xc480000000020021 0xe240000000010010

def z532 : W := mkw 0x40c4800c00940240 0x20624006004a0120 0x0000800c001c0000 0x00004006000e0000

def z533 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x7e7fff0004e18000 0x3f3fff800270c000

def z534 : W := mkw 0xe83858a6cf071772 0x741c2c5367838bb9 0xdef878ffff039fff 0xef7c3c7fff81cfff

def z535 : W := mkw 0xa03050a2c0001530 0x5018285160000a98 0xdcf878e3c0001f38 0xee7c3c71e0000f9c

def z536 : W := mkw 0xc0fff6ffb6b41ec0 0x607ffb7fdb5a0f60 0xbfffe0ff07fc1fc1 0x5ffff07f83fe0fe0

def z537 : W := mkw 0x4000000400040240 0x2000000200020120 0x1000802c031c0700 0x08004016018e0380

def z538 : W := mkw 0x807ff6fbb6011410 0x403ffb7ddb008a08 0x0a7f60c304019818 0x053fb0618200cc0c

def z539 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xb580803c031e67e7 0x5ac0401e018f33f3

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00600004038001 0x270030000201c000

def z541 : W := mkw 0x0020580001030000 0x00102c0000818000 0x4000780000038000 0x20003c000001c000

def z542 : W := mkw 0xd0dfa4fd26f4decd 0x686fd27e937a6f66 0xbfffe0ff07fd9fd9 0x5ffff07f83fecfec

def z543 : W := mkw 0x50c7a45d20f4cacd 0x2863d22e907a6566 0xef87e4df24fff8ff 0xf7c3f26f927ffc7f

def z544 : W := mkw 0x0002240000000000 0x0001120000000000 0x6c07640000000000 0x3603b20000000000

def z545 : W := mkw 0x0108000006d1c001 0x008400000368e000 0x0200000004e18000 0x010000000270c000

def z546 : W := mkw 0x817effa007dbf401 0xc0bf7fd003edfa00 0xffffffe007ffff01 0x7ffffff003ffff80

def z547 : W := mkw 0x0020500280000000 0x0010280140000000 0x40007803c0000000 0xa0003c01e0000000

def z548 : W := mkw 0xa16eff0047dbf531 0xd0b77f8023edfa98 0x7fffff0007ffff39 0x3fffff8003ffff9c

def z549 : W := mkw 0xa01800a2c6001530 0x500c005163000a98 0x9ef800e3c7001f39 0xcf7c0071e3800f9c

def z550 : W := mkw 0x2877fffbf90a2122 0x943bfffdfc851091 0xfc7ffffff8026026 0xfe3ffffffc013013

def z551 : W := mkw 0x0057a6f930000000 0x002bd37c98000000 0xbc7f87fc38000000 0x5e3fc3fe1c000000

def z552 : W := mkw 0xe8ffffffffbe3fe2 0xf47fffffffdf1ff1 0xfffffffffffe7fe7 0xffffffffffff3ff3

def z553 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x1a7f80ec07fc1f00 0x0d3fc07603fe0f80

def z554 : W := mkw 0xb17ffff3e7fbfdbd 0xd8bffff9f3fdfede 0xfffffff3e7ffffff 0xfffffff9f3ffffff

def z555 : W := mkw 0x696cdb044f9f2362 0xb4b66d8227cf91b1 0x10789b2cdb1c0700 0x083c4d966d8e0380

def z556 : W := mkw 0x48000904090e2242 0xa400048204871121 0x75009f1c3b1e60c7 0x3a804f8e1d8f3063

def z557 : W := mkw 0x003150fbb0000000 0x0018a87dd8000000 0xdc7878fff8000000 0xee3c3c7ffc000000

def z558 : W := mkw 0x017effa287dbe001 0x80bf7fd143edf000 0xff7fffe3c7ffe001 0xffbffff1e3fff000

def z559 : W := mkw 0xc8dd81fc0ebc3ec2 0xe46ec0fe075e1f61 0xbfff87fc3ffc7fc7 0x5fffc3fe1ffe3fe3

def z560 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x75809f00031e67e7 0x3ac04f80018f33f3

def z561 : W := mkw 0xa07cdaaad7031530 0x503e6d556b818a98 0x10789b2cdb000700 0x083c4d966d800380

def z562 : W := mkw 0x0177f7fbb0d8e001 0x80bbfbfdd86c7000 0xfd7ffffff8fc6000 0xfebffffffc7e3000

def z563 : W := mkw 0xa077f6fbf0001530 0x503bfb7df8000a98 0xfcfffffff8001f38 0xfe7ffffffc000f9c

def z564 : W := mkw 0x68022d04494ee363 0xb401168224a771b1 0xff87ff3cffffe7e7 0xffc3ff9e7ffff3f3

def z565 : W := mkw 0xc0fff6ffb6941640 0x607ffb7fdb4a0b20 0xfc7ffffffb1c0700 0xfe3ffffffd8e0380

def z566 : W := mkw 0x0001005000000000 0x0000802800000000 0xac0700d000000000 0x5603806800000000

def z567 : W := mkw 0x901b24f12660dc8d 0x480d927893306e46 0xffff64f327e3ffff 0xffffb27993f1ffff

def z568 : W := mkw 0x116fff5127fbe88d 0x88b7ffa893fdf446 0x7f7fff1027ffe0c7 0x3fbfff8813fff063

def z569 : W := mkw 0x001000a000000000 0x0008005000000000 0x9c7800e000000000 0x4e3c007000000000

def z570 : W := mkw 0x100224012040c00d 0x0801120090206006 0x0000040020006006 0x0000020010003003

def z571 : W := mkw 0x4077f6ffb0040240 0x203bfb7fd8020120 0xfdfffffffb1c07c1 0xfefffffffd8e03e0

def z572 : W := mkw 0x690809044fdfe363 0xb484048227eff1b1 0xf7809f3cffffe7e7 0xfbc04f9e7ffff3f3

def z573 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xefff64d324e3f8ff 0xf7ffb2699271fc7f

def z574 : W := mkw 0xd08b245526f4decd 0x6845922a937a6f66 0xef8764d327ffffff 0xf7c3b26993ffffff

def z575 : W := mkw 0x100100512020088c 0x0800802890100446 0xce8060d3240398ff 0xe74030699201cc7f

def z576 : W := mkw 0x6946af0449dee363 0xb4a3578224ef71b1 0xf5879f3cfbfe67e7 0xfac3cf9e7dff33f3

def z577 : W := mkw 0x2000080041020120 0x1000040020810090 0xf5801c30e30267e7 0xfac00e18718133f3

def z578 : W := mkw 0x6866ff04490e2362 0xb4337f82248711b1 0xfdffff3cfb1e67e7 0xfeffff9e7d8f33f3

def z579 : W := mkw 0x01205b00010b2000 0x80902d8000859000 0x00001b0000000000 0x00000d8000000000

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x21000410200060c6 0x1080020810003063

def z581 : W := mkw 0xe83859a6cf0f3772 0xf41c2cd367879bb9 0xdff878e3c71fffff 0xeffc3c71e38fffff

def z582 : W := mkw 0xe0dd88fc47b71ff0 0x706ec47e23db8ff8 0xbfff80fc07ff9ff9 0x5fffc07e03ffcffc

def z583 : W := mkw 0x00000900010a2000 0x8000048000851000 0x10009b00031c0000 0x08004d80018e0000

def z584 : W := mkw 0x007ffefbb7030000 0x003fff7ddb818000 0xfe7fffffff038001 0xff3fffffff81c000

def z585 : W := mkw 0x0076f6a280000000 0x003b7b5140000000 0xfc7fffe3c0000000 0xfe3ffff1e0000000

def z586 : W := mkw 0x100100512020088c 0x0800802890100446 0xaf8700d324e018ff 0xd7c3806992700c7f

def z587 : W := mkw 0xa07ffefbf7031530 0x503fff7dfb818a98 0xdeff78e3c7039f39 0xef7fbc71e381cf9c

def z588 : W := mkw 0x0067f65120000000 0x0033fb2890000000 0xfc7fffd320000000 0xfe3fffe990000000

def z589 : W := mkw 0xc09800a406b41ec0 0x604c0052035a0f60 0x9ff800e007fc1fc1 0x4ffc007003fe0fe0

def z590 : W := mkw 0x0146af0001dae001 0x80a3578000ed7000 0x75079f0003fe6001 0x3a83cf8001ff3000

def z591 : W := mkw 0xe09100fec0241ff0 0x7048807f60120ff8 0x808000ffc0001ff8 0xc040007fe0000ffc

def z592 : W := mkw 0x68032d55690e2362 0xb40196aab48711b1 0xfd87fffffb1e67e7 0xfec3fffffd8f33f3

def z593 : W := mkw 0x017effaa97dbe001 0x80bf7fd54bedf000 0x7f7fff2cdfffe001 0x3fbfff966ffff000

def z594 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x90809b3cfb1c07e6 0xc8404d9e7d8e03f3

def z595 : W := mkw 0x01227f03b14be001 0x80913f81d8a5f000 0x40007f03f803e000 0xa0003f81fc01f000

def z596 : W := mkw 0x0001005000200880 0x0000802800100440 0xef8760d304e398f9 0xf7c3b0698271cc7c

def z597 : W := mkw 0x697fffffffdfe363 0xb4bfffffffeff1b1 0xffffffffffffe7e7 0xfffffffffffff3f3

def z598 : W := mkw 0x100224012060c88d 0x0801120090306446 0x4380640324e3f8ff 0xa1c032019271fc7f

def z599 : W := mkw 0x1108090007fbe88d 0x8884048003fdf446 0x0380000007fff8ff 0x01c0000003fffc7f

def z600 : W := mkw 0xa01008a2c1021530 0x5008045160810a98 0xd48018e3c3021f39 0xea400c71e1810f9c

def z601 : W := mkw 0x000224000040c001 0x0001120000206000 0x400064000003e000 0x200032000001f000

def z602 : W := mkw 0xe81809a44f0e3762 0xf40c04d227871bb1 0xfff89ffcff1e7fe7 0xfffc4ffe7f8f3ff3

def z603 : W := mkw 0x0108090007dbe001 0x8084048003edf000 0x77009f0007ffe001 0x3b804f8003fff000

def z604 : W := mkw 0x003050a280000000 0x0018285140000000 0x087860c300000000 0x043c306180000000

def z605 : W := mkw 0x100324512060c88d 0x0801922890306446 0xee0764d324e19818 0xf703b2699270cc0c

def z606 : W := mkw 0x00022d00014ae001 0x8001168000a57000 0x7f07ff0007ffe001 0x3f83ff8003fff000

def z607 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x5e787820c7038701 0x2f3c3c106381c380

def z608 : W := mkw 0xa07ffefbf7031530 0x503fff7dfb818a98 0xfc7ffffffb000700 0xfe3ffffffd800380

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000003cf8000000 0xc000001e7c000000

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x6500040000026001 0x3280020000013000

def z611 : W := mkw 0xc1fff6fc06f5dec1 0x60fffb7e037aef60 0xbfffe0fc07fd9fc1 0x5ffff07e03fecfe0

def z612 : W := mkw 0x81fff6f806f1dc81 0x40fffb7c0378ee40 0x0a7f60c004e19800 0x053fb0600270cc00

def z613 : W := mkw 0xf83b7df7ef6fffff 0xfc1dbefbf7b7ffff 0xffffffffffffffff 0xffffffffffffffff

def z614 : W := mkw 0x6800000448040362 0x34000002240201b1 0x0000002cd8000700 0x000000166c000380

def z615 : W := mkw 0xc0d580fc00b41ec0 0x606ac07e005a0f60 0xa18780fc00fc1fc0 0x50c3c07e007e0fe0

def z616 : W := mkw 0x78032d55696eebef 0xbc0196aab4b775f7 0xef8764d327ffffff 0xf7c3b26993ffffff

def z617 : W := mkw 0x0022760000000000 0x00113b0000000000 0x40007f0000000000 0x20003f8000000000

def z618 : W := mkw 0xe9fffffc4fffffe3 0xf4fffffe27fffff1 0xfffffffcffffffe7 0xfffffffe7ffffff3

def z619 : W := mkw 0x8088000006b01c80 0x4044000003580e40 0x0200000004e01800 0x0100000002700c00

def z620 : W := mkw 0x010a2d0007dbe001 0x8085168003edf000 0x6f07640007ffe001 0x3783b20003fff000

def z621 : W := mkw 0x48000104080c2242 0xa400008204061121 0xe580871c381e60e7 0xf2c0438e1c0f3073

def z622 : W := mkw 0xe0fffefff7b71ff0 0x707fff7ffbdb8ff8 0xffffffffffff9ff9 0xffffffffffffcffc

def z623 : W := mkw 0xa008080047031530 0x5004040023818a98 0xd6801820c7039f39 0xeb400c106381cf9c

def z624 : W := mkw 0x2000080041020120 0x1000040020810090 0xf4809f3cfb020721 0xfa404f9e7d810390

def z625 : W := mkw 0xf0fffcffe7f7dffd 0x787ffe7ff3fbeffe 0xfffffcffe7ffffff 0xfffffe7ff3ffffff

def z626 : W := mkw 0x0047a65930000000 0x0023d32c98000000 0x0007000000000000 0x0003800000000000

def z627 : W := mkw 0xc01800a406041640 0x600c005203020b20 0xbff880fc071c1fc1 0x5ffc407e038e0fe0

def z628 : W := mkw 0x100000000060c88d 0x0800000000306446 0xcf8060c304e3f8ff 0xe7c030618271fc7f

def z629 : W := mkw 0x20000900410a2120 0x9000048020851090 0xf5809f20c31e6721 0xfac04f90618f3390

def z630 : W := mkw 0xa01000a2c0001530 0x5008005160000a98 0xce8060e3c4039f39 0xe7403071e201cf9c

def z631 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xec7f64d320000000 0xf63fb26990000000

def z632 : W := mkw 0xe83859a6cf0f3772 0xf41c2cd367879bb9 0x10789b2cdb1c0700 0x083c4d966d8e0380

def z633 : W := mkw 0x103374f3a060c88d 0x0819ba79d0306446 0xffff7cf3e4e3f8ff 0xffffbe79f271fc7f

def z634 : W := mkw 0x100100512020088c 0x0800802890100446 0x000000c300001818 0x0000006180000c0c

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0xb400803c00000000 0x5a00401e00000000

def z636 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x6f7f640004e3e001 0x37bfb2000271f000

def z637 : W := mkw 0x68227f07f90e2362 0xb4113f83fc8711b1 0xf580ff3ffb1e67e7 0xfac07f9ffd8f33f3

def z638 : W := mkw 0x28000900490a2122 0x9400048024851091 0xf4009f3cf8026026 0xfa004f9e7c013013

def z639 : W := mkw 0x0028500006010000 0x0014280003008000 0x0a78600004018000 0x053c30000200c000

def z640 : W := mkw 0xa108090047dbf531 0xd084048023edfa98 0x0380000007ffff39 0x01c0000003ffff9c

def z641 : W := mkw 0xb03b7cf3e763ddbd 0x581dbe79f3b1eede 0xdeff78e3c7e39f39 0xef7fbc71e3f1cf9c

def z642 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdc7878e3c3000700 0xee3c3c71e1800380

def z643 : W := mkw 0x110b2d5127fbe88d 0x888596a893fdf446 0xef8764d327fff8ff 0xf7c3b26993fffc7f

def z644 : W := mkw 0x100000000040c00d 0x0800000000206006 0x000000000003e03e 0x000000000001f01f

def z645 : W := mkw 0x6800080449060362 0x34000402248301b1 0xd480183cfb0207e7 0xea400c1e7d8103f3

def z646 : W := mkw 0x801800a006001400 0x400c005003000a00 0x1078002003000700 0x083c001001800380

def z647 : W := mkw 0x807ff6fbb6001400 0x403ffb7ddb000a00 0xfeffffffff001f01 0xff7fffffff800f80

def z648 : W := mkw 0xa000000040001530 0x5000000020000a98 0x0080000000001f38 0x0040000000000f9c

def z649 : W := mkw 0x28000900490a2122 0x9400048024851091 0x0000000000026026 0x0000000000013013

def z650 : W := mkw 0x48c5815c08bc2ac2 0xa462c0ae045e1561 0x2107871c38fc60c6 0x1083c38e1c7e3063

def z651 : W := mkw 0xe0fcd8aec7971770 0x707e6c5763cb8bb8 0x1078982cc31c0700 0x083c4c16618e0380

def z652 : W := mkw 0xc0dd80fc06941640 0x606ec07e034a0b20 0xbc7f80fc031c0700 0x5e3fc07e018e0380

def z653 : W := mkw 0x100100512020088c 0x0800802890100446 0xe58004d3200278ff 0xf2c0026990013c7f

def z654 : W := mkw 0x1147a75120f8e88d 0x88a3d3a8907c7446 0xef87e7d324fff8ff 0xf7c3f3e9927ffc7f

def z655 : W := mkw 0x0077f6f800000000 0x003bfb7c00000000 0xfc7ffffc00000000 0x7e3ffffe00000000

def z656 : W := mkw 0x80dc80a806901400 0x406e405403480a00 0x0078000000000000 0x003c000000000000

def z657 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0x9ef880ec071c1f01 0x4f7c4076038e0f80

def z658 : W := mkw 0x817effa287dbf411 0xc0bf7fd143edfa08 0x7f7fffc307fff819 0x3fbfffe183fffc0c

def z659 : W := mkw 0x000224000040c001 0x0001120000206000 0xef87641024e3e0e7 0xf7c3b2081271f073

def z660 : W := mkw 0x100324512060c88d 0x0801922890306446 0xce8760c304e39839 0xe743b0618271cc1c

def z661 : W := mkw 0xe088080447b71ff0 0x7044040223db8ff8 0x0380000007ff9ff9 0x01c0000003ffcffc

def z662 : W := mkw 0x100324512060c88d 0x0801922890306446 0x8a8760d324e198fe 0xc543b0699270cc7f

def z663 : W := mkw 0x28000900490a2122 0x9400048024851091 0x00001b00d8000000 0x00000d806c000000

def z664 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x4a7f7f0004e3e000 0x253fbf800271f000

def z665 : W := mkw 0xc09100ffb0241ec0 0x6048807fd8120f60 0x808000fff8001fc0 0xc040007ffc000fe0

def z666 : W := mkw 0x116ff65126f1c88d 0x08b7fb289378e446 0x0a7f60c304e19818 0x053fb0618270cc0c

def z667 : W := mkw 0xa01000a2c0001530 0x5008005160000a98 0x00000020c0000700 0x0000001060000380

def z668 : W := mkw 0x803850a286001400 0x401c285143000a00 0xdef878e3c7001f01 0xef7c3c71e3800f80

def z669 : W := mkw 0x0057a4f920000000 0x002bd27c90000000 0xfc7fe4ff20000000 0xfe3ff27f90000000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x40001f00f8000000 0xa0000f807c000000

def z671 : W := mkw 0x41c7a75c00fceac1 0xa0e3d3ae007e7560 0x2107871c00fc60c0 0x1083c38e007e3060

def z672 : W := mkw 0x6800000448040362 0x34000002240201b1 0xb580803cfb1c07e7 0xdac0401e7d8e03f3

def z673 : W := mkw 0x683059a6c90e2362 0xb4182cd3648711b1 0xfdf8fffffb1e67e7 0xfefc7ffffd8f33f3

def z674 : W := mkw 0x500324552064cacd 0x2801922a90326566 0xff87e4ff27ffffff 0xffc3f27f93ffffff

def z675 : W := mkw 0x003276a3b0000000 0x00193b51d8000000 0xdc787fe3f8000000 0xee3c3ff1fc000000

def z676 : W := mkw 0x016cdb0007dbe001 0x80b66d8003edf000 0x13789b0007ffe001 0x09bc4d8003fff000

def z677 : W := mkw 0x903b74f3a661dc9d 0x481dba79d330ee4e 0x0a7f60c304e19818 0x053fb0618270cc0c

def z678 : W := mkw 0x001100fbb0000000 0x0008807dd8000000 0xf4009ffff8000000 0xfa004ffffc000000

def z679 : W := mkw 0x0067f65930000000 0x0033fb2c98000000 0x7c7fff1c38000000 0x3e3fff8e1c000000

def z680 : W := mkw 0x001100fbb0000000 0x0008807dd8000000 0x000000c300000000 0x0000006180000000

def z681 : W := mkw 0xa17cdba2c79b3530 0xd0be6dd163cd9a98 0x10789b20c31c0700 0x083c4d90618e0380

def z682 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xb5809b3cdb1c07c1 0x5ac04d9e6d8e03e0

def z683 : W := mkw 0x4000000400040240 0x2000000200020120 0x2100801c001c00c0 0x1080400e000e0060

def z684 : W := mkw 0x6877fffff90e2362 0xb43bfffffc8711b1 0xfc7ffffffb1c0700 0xfe3ffffffd8e0380

def z685 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x4a7878c3c4039838 0xa53c3c61e201cc1c

def z686 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x2b7f80dc04fc18c0 0x15bfc06e027e0c60

def z687 : W := mkw 0x0020500280010010 0x0010280140008008 0x0000600300018018 0x000030018000c00c

def z688 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xf4009f3cfb1c0700 0xfa004f9e7d8e0380

def z689 : W := mkw 0xa01808a047031530 0x500c045023818a98 0x9ef800e007039f39 0x4f7c00700381cf9c

def z690 : W := mkw 0x017ffff807dbe001 0x80bffffc03edf000 0xff7ffffc07ffe001 0x7fbffffe03fff000

def z691 : W := mkw 0x000324500060c881 0x0001922800306440 0xef8764d004e3f8c1 0x77c3b2680271fc60

def z692 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xd4809b2cdb1e0721 0xea404d966d8f0390

def z693 : W := mkw 0xa17efea2c7d3d531 0x50bf7f5163e9ea98 0xdeff78e3c7e39f39 0xef7fbc71e3f1cf9c

def z694 : W := mkw 0x100324512060c88d 0x0801922890306446 0xaf8760d304e198d9 0x57c3b0698270cc6c

def z695 : W := mkw 0xd1fffffd27fffecd 0xe8fffffe93ffff66 0xffffffff27ffffff 0xffffffff93ffffff

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x74009f0000000000 0x3a004f8000000000

def z697 : W := mkw 0x100224000060c88d 0x0801120000306446 0x6f87640004e3f8ff 0x37c3b2000271fc7f

def z698 : W := mkw 0x682859044f0f2362 0xb4142c82278791b1 0xfff8ff3cff1fe7e7 0xfffc7f9e7f8ff3f3

def z699 : W := mkw 0x0020500000000000 0x0010280000000000 0x5c78780000000000 0x2e3c3c0000000000

def z700 : W := mkw 0xa0285802c7031530 0x50142c0163818a98 0x42807803c7039f39 0xa1403c01e381cf9c

def z701 : W := mkw 0x1047a6593060c88d 0x0823d32c98306446 0xef87e7df3ce3f8ff 0xf7c3f3ef9e71fc7f

def z702 : W := mkw 0xc1eeff0407fffec1 0xe0f77f8203ffff60 0x7fffff0007ffffc1 0x3fffff8003ffffe0

def z703 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x50787823c3038738 0xa83c3c11e181c39c

def z704 : W := mkw 0x005d80f806900000 0x002ec07c03480000 0xbf7f80fc07fc0001 0x5fbfc07e03fe0000

def z705 : W := mkw 0x40c7a65d30b40ac0 0x2063d32e985a0560 0x2107871c38fc00c0 0x1083c38e1c7e0060

def z706 : W := mkw 0x41efff5c07ffeac1 0xa0f7ffae03fff560 0x7f7fff1c07ffe0c1 0x3fbfff8e03fff060

def z707 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x9ef878e3c7019f19 0x4f7c3c71e380cf8c

def z708 : W := mkw 0x011909fbb7dbe001 0x808c84fddbedf000 0x830000ffffffe001 0xc180007ffffff000

def z709 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfcfffffff803f8fe 0xfe7ffffffc01fc7f

def z710 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x5e7ffb0007ff8001 0x2f3ffd8003ffc000

def z711 : W := mkw 0x29227f00494be123 0x94913f8024a5f091 0x40007f00d803e000 0x20003f806c01f000

def z712 : W := mkw 0x4000000400040240 0x2000000200020120 0xf5809f3cfb1e67e7 0xfac04f9e7d8f33f3

def z713 : W := mkw 0xc0dd80fe96b41ec0 0x606ec07f4b5a0f60 0xbfff80fcdffc1fc1 0x5fffc07e6ffe0fe0

def z714 : W := mkw 0x005580f800000000 0x002ac07c00000000 0xbc7f9bfcd8000000 0x5e3fcdfe6c000000

def z715 : W := mkw 0x116eff0127dbe00d 0x88b77f8093edf006 0x7f7fff0027ffe007 0x3fbfff8013fff003

def z716 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x948000fc03001fc1 0x4a40007e01800fe0

def z717 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x7c7fffefd8000000 0x3e3ffff7ec000000

def z718 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfff8f8e3c71f9f39 0xfffc7c71e38fcf9c

def z719 : W := mkw 0xc0dd80fc06941640 0x606ec07e034a0b20 0xbf7f80fc07fc0701 0x5fbfc07e03fe0380

def z720 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff9ffcfffe7fe7 0xffffcffe7fff3ff3

def z721 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xff7ffffffce3f819 0xffbffffffe71fc0c

def z722 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xf7809f3cff1fffff 0xfbc04f9e7f8fffff

def z723 : W := mkw 0x003276a3b0000000 0x00193b51d8000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z724 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fffc307fff819 0x3fbfffe183fffc0c

def z725 : W := mkw 0x004c8900079a2000 0x8026448003cd1000 0x3f7f800007fe6001 0x1fbfc00003ff3000

def z726 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x5e7878e3c7039f19 0x2f3c3c71e381cf8c

def z727 : W := mkw 0x690809044f9f2362 0xb484048227cf91b1 0x01800000031e67e7 0x00c00000018f33f3

def z728 : W := mkw 0x004c800006900000 0x0026400003480000 0xbfff80c007fc1801 0x5fffc06003fe0c00

def z729 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x4af878c3c7039f39 0xa57c3c61e381cf9c

def z730 : W := mkw 0x004c800006900000 0x0026400003480000 0xbfff801007fc00c1 0x5fffc00803fe0060

def z731 : W := mkw 0xa03058a2c1031530 0x50182c5160818a98 0xdcf878e3c0039f38 0xee7c3c71e001cf9c

def z732 : W := mkw 0x0076f6aa9040c001 0x003b7b5548206000 0x7f7fff2cdce3e001 0x3fbfff966e71f000

def z733 : W := mkw 0x0067f65120000000 0x0033fb2890000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z734 : W := mkw 0xa8dd89f84fba3da2 0xd46ec4fc27dd1ed1 0x4a7f1fc0fce27826 0xa53f8fe07e713c13

def z735 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfef87cf3e7039f39 0xff7c3e79f381cf9c

def z736 : W := mkw 0x004ea60006900000 0x0027530003480000 0x3f7f870007fc0001 0x1fbfc38003fe0000

def z737 : W := mkw 0x100324512060c88d 0x0801922890306446 0xff8764f327e3ffff 0xffc3b27993f1ffff

def z738 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff9bfcdffc1fc1 0x5fffcdfe6ffe0fe0

def z739 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xd078fffff8000000 0xe83c7ffffc000000

def z740 : W := mkw 0xd09100ffb0241ecc 0x6848807fd8120f66 0x808000fff8001ffe 0xc040007ffc000fff

def z741 : W := mkw 0xc0dd82fc16b41ec0 0x606ec17e0b5a0f60 0xbfff83fc1ffc1fc1 0x5fffc1fe0ffe0fe0

def z742 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x90789b3cf8000000 0xc83c4d9e7c000000

def z743 : W := mkw 0xc8dd80fc0eb41ec2 0x646ec07e075a0f61 0xbfff80fc3ffc1fc7 0x5fffc07e1ffe0fe3

def z744 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfd7ffffffb1c0001 0xfebffffffd8e0000

def z745 : W := mkw 0x006efe0007930000 0x00377f0003c98000 0x7f7fff0007ff8001 0x3fbfff8003ffc000

def z746 : W := mkw 0x0074d2abb0000000 0x003a6955d8000000 0x10789b2ff8000000 0x883c4d97fc000000

def z747 : W := mkw 0x004c800006900000 0x0026400003480000 0x7f7fe00007ff8001 0x3fbff00003ffc000

def z748 : W := mkw 0x016eff0287dbe011 0x80b77f8143edf008 0x7f7fff0307ffe019 0x3fbfff8183fff00c

def z749 : W := mkw 0xc0aa7607b6b41ec0 0x60553b03db5a0f60 0x43807f03fffc1fc1 0xa1c03f81fffe0fe0

def z750 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xf5809ffffb1e7fff 0xfac04ffffd8f3fff

def z751 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbe7f80fc07fc1f00 0x5f3fc07e03fe0f80

def z752 : W := mkw 0x014ea70006d8e001 0x80a75380036c7000 0x317f870003fc6000 0x18bfc38001fe3000

def z753 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbd7f80fc03fc07c0 0x5ebfc07e01fe03e0

def z754 : W := mkw 0x206cd802c7930130 0x10366c0163c98098 0x7f7ff803c7ff8039 0xbfbffc01e3ffc01c

def z755 : W := mkw 0x680809044f0f2362 0xb4040482278791b1 0x03800000071fe7e7 0x01c00000038ff3f3

def z756 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfcfffffff8020021 0xfe7ffffffc010010

def z757 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x0000003c000007c0 0x0000001e000003e0

def z758 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0xfc7ffbffd8000000 0xfe3ffdffec000000

def z759 : W := mkw 0xc0dd80fd36b41ec0 0x606ec07e9b5a0f60 0xbfff80fc3ffc1fc1 0x5fffc07e1ffe0fe0

def z760 : W := mkw 0x004c800006900000 0x0026400003480000 0x7f7f840007fe6001 0x3fbfc20003ff3000

def z761 : W := mkw 0x6877fffff90e2362 0xb43bfffffc8711b1 0x09ff60c3031e67e7 0x04ffb061818f33f3

def z762 : W := mkw 0x003050a280000000 0x0018285140000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z763 : W := mkw 0x116ddb5127bb288c 0x88b6eda893dd9446 0x90f89bd3231c18fe 0xc87c4de9918e0c7f

def z764 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfefffffffc001801 0xff7ffffffe000c00

def z765 : W := mkw 0x0166f70000d8e001 0x80b37b80006c7000 0x317f9f0000fc6000 0x18bfcf80007e3000

def z766 : W := mkw 0x60e5d85ec1b70bf0 0x3072ec2f60db85f8 0x6107f81fc0ff80f8 0xb083fc0fe07fc07c

def z767 : W := mkw 0x006cd20006900000 0x0036690003480000 0x3f7f9b0007fc0001 0x1fbfcd8003fe0000

def z768 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x757f9f0003fe6001 0x3abfcf8001ff3000

def z769 : W := mkw 0xc09100fd20241ec0 0x6048807e90120f60 0x808000ff20001fc0 0xc040007f90000fe0

def z770 : W := mkw 0x296eff03ffdbe123 0x94b77f81ffedf091 0x7f7fff03ffffe027 0xbfbfff81fffff013

def z771 : W := mkw 0x0076f6aa90000000 0x003b7b5548000000 0xfc7fff3cf8000000 0xfe3fff9e7c000000

def z772 : W := mkw 0x1077f6fbb020088c 0x083bfb7dd8100446 0xfdfffffff80278ff 0xfefffffffc013c7f

def z773 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff2007ffe701 0x7fffff9003fff380

def z774 : W := mkw 0x012a7d0007dbe001 0x80953e8003edf000 0x7f7f7c0007ffe001 0x3fbfbe0003fff000

def z775 : W := mkw 0x0075d2fbb0000000 0x003ae97dd8000000 0xf4789ffff8000000 0xfa3c4ffffc000000

def z776 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x3fff80c007fc1fc1 0x1fffc06003fe0fe0

def z777 : W := mkw 0x803850a286001400 0x401c285143000a00 0xdef878e3c7039f39 0xef7c3c71e381cf9c

def z778 : W := mkw 0x0076f6abb0000000 0x003b7b55d8000000 0x7c7fff2ff8000000 0xbe3fff97fc000000

def z779 : W := mkw 0xc0cc800406941640 0x60664002034a0b20 0x3f7f800007fc0701 0x1fbfc00003fe0380

def z780 : W := mkw 0x003050a280000000 0x0018285140000000 0x10789b2cd8000000 0x083c4d966c000000

def z781 : W := mkw 0xc83851a68e0d3652 0xe41c28d347069b29 0x2b78e7df3c1df8de 0x15bc73ef9e0efc6f

def z782 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0x90789bfcd8000000 0x483c4dfe6c000000

def z783 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x6f7f640007ffe001 0x37bfb20003fff000

def z784 : W := mkw 0x0076f6aa90000000 0x003b7b5548000000 0x187ffb2cd8000000 0x0c3ffd966c000000

def z785 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfdfffffff8e078fe 0xfefffffffc703c7f

def z786 : W := mkw 0xd09324fd2064decd 0x6849927e90326f66 0xc08064ff2003fffe 0xe040327f9001ffff

def z787 : W := mkw 0xa03050a2c0001530 0x5018285160000a98 0xdef878e3c4039f39 0xef7c3c71e201cf9c

def z788 : W := mkw 0x0075d2fbb0000000 0x003ae97dd8000000 0x10789befd8000000 0x083c4df7ec000000

def z789 : W := mkw 0xc89100fc08241ec2 0x6448807e04120f61 0x808000fc38001fc6 0x4040007e1c000fe3

def z790 : W := mkw 0x803850a286011410 0x401c285143008a08 0xdef860e307039f39 0xef7c30718381cf9c

def z791 : W := mkw 0x78032d55696eebef 0xbc0196aab4b775f7 0x1a07fbefdffd9f18 0x0d03fdf7effecf8c

def z792 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xff7ffffffce1f8de 0xffbffffffe70fc6f

def z793 : W := mkw 0xe89100fc48241fe2 0x7448807e24120ff1 0x808000fc00001fe6 0x4040007e00000ff3

def z794 : W := mkw 0x781100fff8240bee 0x3c08807ffc1205f7 0x808000fff8001ffe 0xc040007ffc000fff

def z795 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfc7ffffff8e00000 0xfe3ffffffc700000

def z796 : W := mkw 0xa156a7a2c0d8f531 0xd0ab53d1606c7a98 0xa18787e3c0fc7f38 0xd0c3c3f1e07e3f9c

def z797 : W := mkw 0x1077f6fbb040c00d 0x083bfb7dd8206006 0xfc7ffffff8006006 0xfe3ffffffc003003

def z798 : W := mkw 0x0076f6abb0000000 0x003b7b55d8000000 0x10789f2cf8000000 0x083c4f967c000000

def z799 : W := mkw 0x1077f6fbb040c00d 0x083bfb7dd8206006 0xfc7ffffff8018018 0xfe3ffffffc00c00c

def z800 : W := mkw 0x316eff03e7dbe13d 0x98b77f81f3edf09e 0x7f7fff03e7ffe03f 0xbfbfff81f3fff01f

def z801 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x3f7f803c07fc07c1 0x1fbfc01e03fe03e0

def z802 : W := mkw 0x696ef6044ed5c363 0x34b77b02276ae1b1 0x8aff603cfce187e6 0xc57fb01e7e70c3f3

def z803 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x000000ec00001f00 0x0000007600000f80

def z804 : W := mkw 0x016eff0137dbe001 0x80b77f809bedf000 0x7f7fff003fffe001 0x3fbfff801ffff000

def z805 : W := mkw 0x014eaf0007dae001 0x80a7578003ed7000 0x7f7f9f0007fe6001 0x3fbfcf8003ff3000

def z806 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x0a7f00c007fc1f00 0x053f806003fe0f80

def z807 : W := mkw 0x014c800006d1c001 0x00a640000368e000 0x3f7f800007fd8001 0x1fbfc00003fec000

def z808 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xd0f878e3c3039f38 0xe87c3c71e181cf9c

def z809 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfc7ffffff8038038 0xfe3ffffffc01c01c

def z810 : W := mkw 0x004c880007930000 0x0026440003c98000 0x3f7f800007ff8001 0x1fbfc00003ffc000

def z811 : W := mkw 0xc1b37ffc016ffec1 0xe0d9bffe00b7ff60 0xc0807ffc0003ffc0 0x60403ffe0001ffe0

def z812 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x3b7f80fc07fc1fc0 0x1dbfc07e03fe0fe0

def z813 : W := mkw 0x016ef70006d9e001 0x80b77b80036cf000 0x6f7fe70004ffe001 0x37bff380027ff000

def z814 : W := mkw 0x0077f6fa90000000 0x003bfb7d48000000 0xfc7ffffcd8000000 0x7e3ffffe6c000000

def z815 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfe7ffffffc019818 0xff3ffffffe00cc0c

def z816 : W := mkw 0x014c890007dbe001 0x80a6448003edf000 0x0b7f000007ffe001 0x05bf800003fff000

def z817 : W := mkw 0xe09100fff0241ff0 0x7048807ff8120ff8 0x808000fff8001ff8 0xc040007ffc000ffc

def z818 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffffe0ff07fc1fc1 0xfffff07f83fe0fe0

def z819 : W := mkw 0x0166ff0001dae001 0x80b37f8000ed7000 0x7d7fff0003fe6001 0x3ebfff8001ff3000

def z820 : W := mkw 0x004c800006900000 0x0026400003480000 0x1a7f800007fc0000 0x0d3fc00003fe0000

def z821 : W := mkw 0x100326513060c88d 0x0801932898306446 0xef8767d33ce3f8ff 0xf7c3b3e99e71fc7f

def z822 : W := mkw 0x104ea40126d0c00d 0x0827520093686006 0x7f7fe40327ffe03f 0xbfbff20193fff01f

def z823 : W := mkw 0x004c800006900000 0x0026400003480000 0xffff841027fe60e7 0xffffc20813ff3073

def z824 : W := mkw 0x1074d2aa9060c88d 0x083a695548306446 0x13f89b2cdce3f8ff 0x09fc4d966e71fc7f

def z825 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xff809ffcff1e7fe7 0xffc04ffe7f8f3ff3

def z826 : W := mkw 0x31227f03e14be13d 0x98913f81f0a5f09e 0x40007f03e003e03e 0xa0003f81f001f01f

def z827 : W := mkw 0x1077f6fbb040c00d 0x083bfb7dd8206006 0xff7ffffffce3e03f 0xffbffffffe71f01f

def z828 : W := mkw 0x0075d2fbb0000000 0x003ae97dd8000000 0xdc78fbfff8000000 0xee3c7dfffc000000

def z829 : W := mkw 0x100324512060c88d 0x0801922890306446 0x6b0764d324e3f8fe 0xb583b2699271fc7f

def z830 : W := mkw 0x816eff0007dbf401 0xc0b77f8003edfa00 0x7fffff0007ffff01 0x3fffff8003ffff80

def z831 : W := mkw 0xe88809044fbe3fe2 0xf444048227df1ff1 0x0380000007fc1fc1 0x01c0000003fe0fe0

def z832 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0x317f9f3cf8e060c6 0x18bfcf9e7c703063

def z833 : W := mkw 0x405d80fc06940240 0x202ec07e034a0120 0xbfff80fc07fc07c1 0x5fffc07e03fe03e0

def z834 : W := mkw 0xc09100fd30241ec0 0x6048807e98120f60 0x808000fc38001fc0 0x4040007e1c000fe0

def z835 : W := mkw 0x0044800000000000 0x0022400000000000 0xfc7f9f3cf8000000 0xfe3fcf9e7c000000

def z836 : W := mkw 0x803850a286011410 0x401c285143008a08 0x1a7860e307019f18 0x0d3c30718380cf8c

def z837 : W := mkw 0x100324512060c88d 0x0801922890306446 0xca8764d324e3f8fe 0xe543b2699271fc7f

def z838 : W := mkw 0xe98809044fffffe3 0xf4c4048227fffff1 0x0380000007ffffe7 0x01c0000003fffff3

def z839 : W := mkw 0x006cd00006910000 0x0036680003488000 0x3f7fe00007fd8001 0x1fbff00003fec000

def z840 : W := mkw 0x50c7a65d30f4cacd 0x2863d32e987a6566 0x2107871c38fc60c6 0x1083c38e1c7e3063

def z841 : W := mkw 0x100324512060c88d 0x0801922890306446 0xff87e4d327fff8ff 0xffc3f26993fffc7f

def z842 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff1027ffe001 0xffbfff8813fff000

def z843 : W := mkw 0x0077f6fbb0900000 0x003bfb7dd8480000 0xfd7ffffff8fc0000 0xfebffffffc7e0000

def z844 : W := mkw 0xc0dc80a406b41ec0 0x606e4052035a0f60 0xbfff80e007fc1fc1 0x5fffc07003fe0fe0

def z845 : W := mkw 0x1077f6fbb020088c 0x083bfb7dd8100446 0xfc7ffffff80000c6 0xfe3ffffffc000063

def z846 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xd0809f3cfb1e67e6 0xe8404f9e7d8f33f3

def z847 : W := mkw 0xe80809044f0f3772 0xf404048227879bb9 0x01800000031e67e7 0x00c00000018f33f3

def z848 : W := mkw 0x1067f6512060c88d 0x0833fb2890306446 0xfffffffffce3f8ff 0xfffffffffe71fc7f

def z849 : W := mkw 0x51c7a75d20fceacd 0xa8e3d3ae907e7566 0x2107871c20fc60c6 0x1083c38e107e3063

def z850 : W := mkw 0x0177f6fbb0d0c001 0x00bbfb7dd8686000 0xfc7ffffff8e00000 0xfe3ffffffc700000

def z851 : W := mkw 0xc05c80a406941640 0x602e4052034a0b20 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z852 : W := mkw 0x100100500060c88d 0x0800802800306446 0xef8760d304e3f8ff 0xf7c3b0698271fc7f

def z853 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdef8fbefdf039f39 0xef7c7df7ef81cf9c

def z854 : W := mkw 0x100324512060c88d 0x0801922890306446 0xef877fd3fce3f8ff 0xf7c3bfe9fe71fc7f

def z855 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff80fc07ff9ff9 0x5fffc07e03ffcffc

def z856 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x1a7fe00007fd8000 0x0d3ff00003fec000

def z857 : W := mkw 0x014eaf0007dbe001 0x80a7578003edf000 0x3f7f870007ffe001 0x1fbfc38003fff000

def z858 : W := mkw 0x21227f00414be131 0x90913f8020a5f098 0x40007f000003e038 0x20003f800001f01c

def z859 : W := mkw 0xa03850a2c6011530 0x501c285163008a98 0x0a7860e3c4019f18 0x053c3071e200cf8c

def z860 : W := mkw 0x103374f3a060c88d 0x0819ba79d0306446 0xfffffffffce3f8ff 0xfffffffffe71fc7f

def z861 : W := mkw 0xd0dd80ffb6b41ecc 0x686ec07fdb5a0f66 0xbfff80fffffc1fff 0xdfffc07ffffe0fff

def z862 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x387ffffff8000000 0x1c3ffffffc000000

def z863 : W := mkw 0xe90809044fdff773 0xf484048227effbb9 0x0380000007ffffff 0x01c0000003ffffff

def z864 : W := mkw 0x805c80a006901400 0x402e405003480a00 0x3f7f802007fc0701 0x1fbfc01003fe0380

def z865 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff80fcfffc1fc1 0xdfffc07e7ffe0fe0

def z866 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xc87f7ffff8000000 0xe43fbffffc000000

def z867 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3f7f9f0007fc6001 0x1fbfcf8003fe3000

def z868 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xf5f89f3cf80260e7 0xfafc4f9e7c013073

def z869 : W := mkw 0xd0dd80fd26b41ecc 0x686ec07e935a0f66 0xffff84ff27fe7fff 0xffffc27f93ff3fff

def z870 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x587fffeff8000000 0xac3ffff7fc000000

def z871 : W := mkw 0x001000a000000000 0x0008005000000000 0xfc789ffcf8000000 0xfe3c4ffe7c000000

def z872 : W := mkw 0x004c800006900000 0x0026400003480000 0x7f7f9f0007fc0001 0x3fbfcf8003fe0000

def z873 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff0007ffe021 0xffffff8003fff010

def z874 : W := mkw 0x216eff0047dbe121 0x90b77f8023edf090 0xffffffe3c7ffff39 0xfffffff1e3ffff9c

def z875 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x5f7f780007ffe001 0x2fbfbc0003fff000

def z876 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x717fff0003ffe000 0x38bfff8001fff000

def z877 : W := mkw 0x0077f6fbb0200880 0x003bfb7dd8100440 0xfffffffffce278e7 0xfffffffffe713c73

def z878 : W := mkw 0x016ef70006d9e001 0x80b77b80036cf000 0x7f7fff0004fde000 0x3fbfff80027ef000

def z879 : W := mkw 0x0077f6fbb0200880 0x003bfb7dd8100440 0xfd7ffffff8e000c0 0xfebffffffc700060

def z880 : W := mkw 0xa04fae5977031530 0x5027d72cbb818a98 0x2287871c3f039f39 0x1143c38e1f81cf9c

def z881 : W := mkw 0x404c800406940240 0x20264002034a0120 0x3f7f802c07fc0701 0x1fbfc01603fe0380

def z882 : W := mkw 0xa03858a2c7931530 0x501c2c5163c98a98 0xdff878e3c7ff9f39 0xeffc3c71e3ffcf9c

def z883 : W := mkw 0x40d580fc00b40ac0 0x206ac07e005a0560 0xbdff80fc03fc07c1 0x5effc07e01fe03e0

def z884 : W := mkw 0x680809044f9e2362 0xb404048227cf11b1 0x0380000007fe67e7 0x01c0000003ff33f3

def z885 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff84fc07fe7fc1 0x7fffc27e03ff3fe0

def z886 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff3cffffe0e7 0xffffff9e7ffff073

def z887 : W := mkw 0x014c8900079b2000 0x80a6448003cd9000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z888 : W := mkw 0x216eff02c7dbe131 0x90b77f8163edf098 0xffffffc3c7fff839 0xffffffe1e3fffc1c

def z889 : W := mkw 0x296eff004fdbe123 0x94b77f8027edf091 0x7f7fff00dfffe001 0x3fbfff806ffff000

def z890 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x1a7f9b0007fc0000 0x0d3fcd8003fe0000

def z891 : W := mkw 0xc0cd805406b41ec0 0x6066c02a035a0f60 0xbfff80d007fc1fc1 0x5fffc06803fe0fe0

def z892 : W := mkw 0xc09100ffb0241ec0 0x6048807fd8120f60 0x808000ff00001fc0 0x4040007f80000fe0

def z893 : W := mkw 0x0077f6fbb0200880 0x003bfb7dd8100440 0xfcfffffff80018c0 0xfe7ffffffc000c60

def z894 : W := mkw 0x803850a286011410 0x401c285143008a08 0x0af860c307019f19 0x057c30618380cf8c

def z895 : W := mkw 0x690a2d044fdfe363 0xb485168227eff1b1 0xef87641027ffe7e7 0xf7c3b20813fff3f3

def z896 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x2b7fe70007ffe001 0x15bff38003fff000

def z897 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0xe58004fc20027fe7 0xf2c0027e10013ff3

def z898 : W := mkw 0x003376fbb0000000 0x0019bb7dd8000000 0xdc787ffff8000000 0xee3c3ffffc000000

def z899 : W := mkw 0x0077f6fbb040c001 0x003bfb7dd8206000 0xfe7ffffffce18000 0xff3ffffffe70c000

def z900 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfff8ffffff03ffff 0xfffc7fffff81ffff

def z901 : W := mkw 0x80f7f6fbb0201c80 0x407bfb7dd8100e40 0xfc7ffffff8001800 0xfe3ffffffc000c00

def z902 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xf47f9f3cf8000000 0xfa3fcf9e7c000000

def z903 : W := mkw 0x116eff0127dbe00d 0x88b77f8093edf006 0xffffffc327fff83f 0xffffffe193fffc1f

def z904 : W := mkw 0xa03850a2c6011530 0x501c285163008a98 0xcef860e3c4039f39 0xe77c3071e201cf9c

def z905 : W := mkw 0x0077f6f800000000 0x003bfb7c00000000 0xfc7ffffcf8000000 0xfe3ffffe7c000000

def z906 : W := mkw 0x90fff6fbb6f0dc8d 0x487ffb7ddb786e46 0x0a7f60c304e19818 0x053fb0618270cc0c

def z907 : W := mkw 0xe09100fc40241fe0 0x7048807e20120ff0 0x808000fcc0001fe0 0xc040007e60000ff0

def z908 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7fffff0007fff839 0x3fffff8003fffc1c

def z909 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x1bff80ec07fc1fc1 0x0dffc07603fe0fe0

def z910 : W := mkw 0x003150fbb0000000 0x0018a87dd8000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z911 : W := mkw 0xf09100ffe0241ffc 0x7848807ff0120ffe 0x808000ffe0001ffe 0xc040007ff0000fff

def z912 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x107f9b2cd8000000 0x083fcd966c000000

def z913 : W := mkw 0xa83859a2cf0b3532 0xd41c2cd167859a99 0xfff8ffe3ff1fff3f 0xfffc7ff1ff8fff9f

def z914 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff84fc27fc7fc7 0x5fffc27e13fe3fe3

def z915 : W := mkw 0xd0dea4ad26d4d64d 0x686f5256936a6b26 0x5078e42f231fe73e 0xa83c7217918ff39f

def z916 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x8af860e3c7039f39 0xc57c3071e381cf9c

def z917 : W := mkw 0x21227f00414be121 0x90913f8020a5f090 0x40007f00c003e020 0xa0003f806001f010

def z918 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff1c3fffe001 0x3fbfff8e1ffff000

def z919 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x74789f2cd8000000 0x3a3c4f966c000000

def z920 : W := mkw 0xa03859a2c70b3530 0xd01c2cd163859a98 0xdef87fe3c703ff39 0xef7c3ff1e381ff9c

def z921 : W := mkw 0xe09100fec0241ff0 0x7048807f60120ff8 0x808000fcc0001fc0 0x4040007e60000fe0

def z922 : W := mkw 0x00f7f6fbb0b00880 0x007bfb7dd8580440 0xfc7ffffff8e00000 0xfe3ffffffc700000

def z923 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x808000fcf8001fc0 0xc040007e7c000fe0

def z924 : W := mkw 0x0076f6abb0000000 0x003b7b55d8000000 0xf478ff3ff8000000 0xfa3c7f9ffc000000

def z925 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff9ffc07fc1fc1 0x7fffcffe03fe0fe0

def z926 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x1af878e3c7039f39 0x0d7c3c71e381cf9c

def z927 : W := mkw 0xa16eff0047dbf531 0xd0b77f8023edfa98 0xffffffc307ffff39 0xffffffe183ffff9c

def z928 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x9c789becd8000000 0x4e3c4df66c000000

def z929 : W := mkw 0x004c8900079a2000 0x8026448003cd1000 0x3f7f9b0007fc0001 0x1fbfcd8003fe0000

def z930 : W := mkw 0xd0dd80fc06b41ecc 0x686ec07e035a0f66 0xbfff80fc07fc1fff 0x5fffc07e03fe0fff

def z931 : W := mkw 0x296eff004fdbe123 0x94b77f8027edf091 0xffffff20ffffe727 0xffffff907ffff393

def z932 : W := mkw 0x0076f6abb0000000 0x003b7b55d8000000 0x1078fb2fd8000000 0x083c7d97ec000000

def z933 : W := mkw 0x0064d20000000000 0x0032690000000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z934 : W := mkw 0xc0dd80ffb6b41ec0 0x606ec07fdb5a0f60 0xbfff80ff07fc1fc1 0x5fffc07f83fe0fe0

def z935 : W := mkw 0xa03858aad7031530 0x501c2c556b818a98 0xdef878efdf039f39 0xef7c3c77ef81cf9c

def z936 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfe7ffffffce3f83e 0xff3ffffffe71fc1f

def z937 : W := mkw 0x296eff004fdbe123 0x94b77f8027edf091 0xff7fff3cffffe027 0xffbfff9e7ffff013

def z938 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x9eff80ec07fc1f01 0x4f7fc07603fe0f80

def z939 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0x1a7f802c07fc0700 0x0d3fc01603fe0380

def z940 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfffe0ff07fd9fd9 0x5ffff07f83fecfec

def z941 : W := mkw 0x216eff0047dbe131 0x90b77f8023edf098 0x7f7fff0007ffe039 0x3fbfff8003fff01c

def z942 : W := mkw 0xa01808a047021520 0x500c045023810a90 0xdef878e3c7039f39 0xef7c3c71e381cf9c

def z943 : W := mkw 0x0064d20000000000 0x0032690000000000 0x10789b2cd8000000 0x083c4d966c000000

def z944 : W := mkw 0xd0dd80fd26b41ecc 0x686ec07e935a0f66 0xbfff80fc27fc1fc7 0x5fffc07e13fe0fe3

def z945 : W := mkw 0x1076f6abb040c00d 0x083b7b55d8206006 0x5078ff2ff803e03e 0xa83c7f97fc01f01f

def z946 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xffff78e3c7e39f39 0xffffbc71e3f1cf9c

def z947 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3b7fff0007fde000 0x1dbfff8003fef000

def z948 : W := mkw 0x016eff03b7dbe001 0x80b77f81dbedf000 0xff7fff3fffffe001 0xffbfff9ffffff000

def z949 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xf580ff3ffb1fe7ff 0xfac07f9ffd8ff3ff

def z950 : W := mkw 0x40cd805c06b40ac0 0x2066c02e035a0560 0xbfff803c07fc07c1 0x5fffc01e03fe03e0

def z951 : W := mkw 0x100324512060c88d 0x0801922890306446 0x4b8764c324e3f8ff 0xa5c3b2619271fc7f

def z952 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x107f802c03fc0700 0x083fc01601fe0380

def z953 : W := mkw 0x0066ff00014ae001 0x80337f8000a57000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z954 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfcfffffff80000e6 0xfe7ffffffc000073

def z955 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x30789f3cf8000000 0x183c4f9e7c000000

def z956 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0xbfff80ec07fc1f01 0x5fffc07603fe0f80

def z957 : W := mkw 0xf89100fd68241fee 0x7c48807eb4120ff7 0x808000fff8001ffe 0xc040007ffc000fff

def z958 : W := mkw 0x216eff0047dbe121 0x90b77f8023edf090 0x7f7fff00c7ffe021 0xbfbfff8063fff010

def z959 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x50789f2cf8000000 0xa83c4f967c000000

def z960 : W := mkw 0x1077f6fbb020088c 0x083bfb7dd8100446 0xfc7ffffff8001818 0xfe3ffffffc000c0c

def z961 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x1b7ffb0007ffe001 0x0dbffd8003fff000

def z962 : W := mkw 0x016eff0287dbe001 0x80b77f8143edf000 0x7f7fff03c7ffe001 0xbfbfff81e3fff000

def z963 : W := mkw 0x0066f60000000000 0x00337b0000000000 0x7c7fff2cd8000000 0x3e3fff966c000000

def z964 : W := mkw 0xc09100fe80241ec0 0x6048807f40120f60 0x808000ffc0001fc0 0xc040007fe0000fe0

def z965 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfd7ffffff8e3e0fe 0xfebffffffc71f07f

def z966 : W := mkw 0x0067f65bb0000000 0x0033fb2dd8000000 0x7c7fff1ff8000000 0xbe3fff8ffc000000

def z967 : W := mkw 0x396eff016fdbe12f 0x9cb77f80b7edf097 0x7f7fff03ffffe03f 0xbfbfff81fffff01f

def z968 : W := mkw 0x216eff0047dbe121 0x90b77f8023edf090 0xffffff30e7ffe7e7 0xffffff9873fff3f3

def z969 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x90789befd8000000 0xc83c4df7ec000000

def z970 : W := mkw 0x0075d2fa90200880 0x003ae97d48100440 0xbfff9bfcdce018c1 0x5fffcdfe6e700c60

def z971 : W := mkw 0xa04c880047931530 0x5026440023c98a98 0x3fff800007ff9f39 0x1fffc00003ffcf9c

def z972 : W := mkw 0xe89100fc48241fe2 0x7448807e24120ff1 0x808000fcd8001fc0 0x4040007e6c000fe0

def z973 : W := mkw 0x004c800006900000 0x0026400003480000 0xbfff802007fc0701 0x5fffc01003fe0380

def z974 : W := mkw 0x014c830006982000 0x80a64180034c1000 0x3f7f830007fc0001 0x1fbfc18003fe0000

def z975 : W := mkw 0xd09100fd20241ecc 0x6848807e90120f66 0x808000fc20001fc6 0x4040007e10000fe3

def z976 : W := mkw 0x0001005000200880 0x0000802800100440 0xef8764d324e3f8ff 0xf7c3b2699271fc7f

def z977 : W := mkw 0x014c890007dbe001 0x80a6448003edf000 0x7f7f9f0007ffe001 0x3fbfcf8003fff000

def z978 : W := mkw 0xc09100fe80241ed0 0x6048807f40120f68 0x808000ff00001fd8 0x4040007f80000fec

def z979 : W := mkw 0x0075d2fbb0000000 0x003ae97dd8000000 0xbc7f9bfff8000000 0xde3fcdfffc000000

def z980 : W := mkw 0xf88809044ffeffef 0xfc44048227ff7ff7 0x0380000007ffffff 0x01c0000003ffffff

def z981 : W := mkw 0x0057a6f930000000 0x002bd37c98000000 0xfc7f9ffcf8000000 0xfe3fcffe7c000000

def z982 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfef8ffe3c7039f39 0xff7c7ff1e381cf9c

def z983 : W := mkw 0x116eff0127dbe00d 0x88b77f8093edf006 0x7f7fff0307ffe019 0x3fbfff8183fff00c

def z984 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfffffffffce078c7 0xfffffffffe703c63

def z985 : W := mkw 0xb03b7cf3e763ddbd 0x581dbe79f3b1eede 0x317f1c30e3e067c6 0x18bf8e1871f033e3

def z986 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfd7ffffff80060c6 0xfebffffffc003063

def z987 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0xf4809ffcf8001fc0 0xfa404ffe7c000fe0

def z988 : W := mkw 0x0077f6fbb0200880 0x003bfb7dd8100440 0xfffffffffce398f9 0xfffffffffe71cc7c

def z989 : W := mkw 0x690809044f9f2362 0xb484048227cf91b1 0x00000000031c0700 0x00000000018e0380

def z990 : W := mkw 0x003050a280000000 0x0018285140000000 0xfff8fffffc03f8ff 0xfffc7ffffe01fc7f

def z991 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfcfffffff8001838 0xfe7ffffffc000c1c

def z992 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x107f9b0003fc0000 0x083fcd8001fe0000

def z993 : W := mkw 0x0076f6aa90000000 0x003b7b5548000000 0xfc7fffefd8000000 0xfe3ffff7ec000000

def z994 : W := mkw 0x216eff03f7dbe131 0x90b77f81fbedf098 0x7f7fff03ffffe039 0xbfbfff81fffff01c

def z995 : W := mkw 0x5847a75d386ceacf 0xac23d3ae9c367567 0x2107871c38fc60c6 0x1083c38e1c7e3063

def z996 : W := mkw 0x006ef60006900000 0x00377b0003480000 0x3f7fe00007fc0001 0x1fbff00003fe0000

def z997 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x0b7f600007fd8001 0x05bfb00003fec000

def z998 : W := mkw 0x004c880007920000 0x0026440003c90000 0x7f7f980007fe0001 0x3fbfcc0003ff0000

def z999 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xafff00d007fc1fc1 0x57ff806803fe0fe0

def z1000 : W := mkw 0x100324512060c88d 0x0801922890306446 0x2b8764d324e3f8ff 0x15c3b2699271fc7f

def z1001 : W := mkw 0x100324512060c88d 0x0801922890306446 0xff877cf3e4e3f8ff 0xffc3be79f271fc7f

def z1002 : W := mkw 0xa83859a2cf0b3532 0xd41c2cd167859a99 0xdef878e3c703ff3f 0xef7c3c71e381ff9f

def z1003 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xff80ff3cff1fe7e7 0xffc07f9e7f8ff3f3

def z1004 : W := mkw 0x790809044fffebef 0xbc84048227fff5f7 0x0380000007ffffff 0x01c0000003ffffff

def z1005 : W := mkw 0x68000904490f2372 0xb4000482248791b9 0xf5809f3cfb1fe7ff 0xfac04f9e7d8ff3ff

def z1006 : W := mkw 0x216eff02c7dbe131 0x90b77f8163edf098 0xffffff23c7ffe739 0xffffff91e3fff39c

def z1007 : W := mkw 0x803850a286011410 0x401c285143008a08 0xdef878e3c7019f19 0xef7c3c71e380cf8c

def z1008 : W := mkw 0xa03850a2c6011530 0x501c285163008a98 0x9ef860e3c7019f39 0xcf7c3071e380cf9c

def z1009 : W := mkw 0xc0dd80fe86b41ec0 0x606ec07f435a0f60 0xbfff80ffc7fc1fc1 0xdfffc07fe3fe0fe0

def z1010 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x8e8000fc04001fc1 0x4740007e02000fe0

def z1011 : W := mkw 0x0166f70000d8e001 0x80b37b80006c7000 0x7f7fff0004ffe001 0x3fbfff80027ff000

def z1012 : W := mkw 0x014ead0007dbe001 0x80a7568003edf000 0x7f7fe40007ffe001 0x3fbff20003fff000

def z1013 : W := mkw 0x0057a4f920000000 0x002bd27c90000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1014 : W := mkw 0xc09100fe90241ec0 0x6048807f48120f60 0x808000fcd8001fc0 0x4040007e6c000fe0

def z1015 : W := mkw 0xa16eff0047dbf531 0xd0b77f8023edfa98 0xffffff20c7ffff39 0xffffff9063ffff9c

def z1016 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xbc7f9ffcf8000000 0x5e3fcffe7c000000

def z1017 : W := mkw 0x0077f6fbb040c001 0x003bfb7dd8206000 0xfd7ffffff8e06000 0xfebffffffc703000

def z1018 : W := mkw 0xe09100fc40241ff0 0x7048807e20120ff8 0x808000fc00001ff8 0x4040007e00000ffc

def z1019 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xdef8fbefdc039839 0xef7c7df7ee01cc1c

def z1020 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xcef860c307039f39 0xe77c30618381cf9c

def z1021 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x5a7fff0007ffe000 0x2d3fff8003fff000

def z1022 : W := mkw 0x016ef70006d9e001 0x80b77b80036cf000 0x0a7fe30004fd8000 0x053ff180027ec000

def z1023 : W := mkw 0xc0dc80ac06b41ec0 0x606e4056035a0f60 0x3fff802c07fc1fc1 0x1fffc01603fe0fe0

def z1024 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdef878f3e7039fff 0xef7c3c79f381cfff

def z1025 : W := mkw 0xa16eff0047dbf531 0xd0b77f8023edfa98 0x7f7fff0007ffe701 0x3fbfff8003fff380

def z1026 : W := mkw 0x38227f03f94ae12f 0x9c113f81fca57097 0x40007f03f803e03e 0xa0003f81fc01f01f

def z1027 : W := mkw 0xa03859a2c70b3530 0xd01c2cd163859a98 0xdef8fbe3c71f9f39 0xef7c7df1e38fcf9c

def z1028 : W := mkw 0xf80809044f6fffff 0xfc04048227b7ffff 0x0380000007ffffff 0x01c0000003ffffff

def z1029 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xfd80fffffb1e67e7 0xfec07ffffd8f33f3

def z1030 : W := mkw 0xc0cc800406b41ec0 0x60664002035a0f60 0x0bff000007fc1fc1 0x05ff800003fe0fe0

def z1031 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x2b7fe00004fd8000 0x15bff000027ec000

def z1032 : W := mkw 0x016cd20006910000 0x00b6690003488000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z1033 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff80fc07fe7fe7 0x5fffc07e03ff3ff3

def z1034 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x808000ff00001ff8 0xc040007f80000ffc

def z1035 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x5ef878c307039f39 0x2f7c3c618381cf9c

def z1036 : W := mkw 0x39227f01694be12f 0x9c913f80b4a5f097 0x40007f03f803e03e 0xa0003f81fc01f01f

def z1037 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x5c78fb2cd8000000 0x2e3c7d966c000000

def z1038 : W := mkw 0xe89109fc492e3fe2 0xf44884fe24971ff1 0xc0801ffcf8027fe6 0xe0400ffe7c013ff3

def z1039 : W := mkw 0x100324512060c88d 0x0801922890306446 0xef87e7df3ce3f8ff 0xf7c3f3ef9e71fc7f

def z1040 : W := mkw 0xd09100fc00241ecc 0x6848807e00120f66 0x808000fc00001ffe 0x4040007e00000fff

def z1041 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0xb48080fc00001fc0 0x5a40407e00000fe0

def z1042 : W := mkw 0x016ef70006d8e001 0x80b77b80036c7000 0x7f7fff0007fc6001 0x3fbfff8003fe3000

def z1043 : W := mkw 0x8077f6fbb0001410 0x403bfb7dd8000a08 0xfc7ffffff8001818 0xfe3ffffffc000c0c

def z1044 : W := mkw 0xf88b2d556ffeffef 0xfc4596aab7ff7ff7 0xef8764d327ffffff 0xf7c3b26993ffffff

def z1045 : W := mkw 0x1077f6fbb000000c 0x083bfb7dd8000006 0xfc7ffffff800003e 0xfe3ffffffc00001f

def z1046 : W := mkw 0x0020500000000000 0x0010280000000000 0xfc78ff3cf8000000 0xfe3c7f9e7c000000

def z1047 : W := mkw 0x004ead0007dae001 0x8027568003ed7000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z1048 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfff878f3c7039ff9 0xfffc3c79e381cffc

def z1049 : W := mkw 0x016eff03b7dbe001 0x80b77f81dbedf000 0x7f7fff0307ffe001 0x3fbfff8183fff000

def z1050 : W := mkw 0x0076f6a280000000 0x003b7b5140000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1051 : W := mkw 0x006ef603b6900000 0x00377b01db480000 0x7f7fff03fffc0001 0xbfbfff81fffe0000

def z1052 : W := mkw 0xc0dd80fd26b41ec0 0x606ec07e935a0f60 0xbfff80ff27fc1fc1 0xdfffc07f93fe0fe0

def z1053 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x337f9f0007ffe001 0x19bfcf8003fff000

def z1054 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff20c7ffe001 0xffbfff9063fff000

def z1055 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0x317f802c03fc0700 0x18bfc01601fe0380

def z1056 : W := mkw 0xe88809044f9e3762 0xf444048227cf1bb1 0x00000000031c0700 0x00000000018e0380

def z1057 : W := mkw 0x38227d03e94be13f 0x9c113e81f4a5f09f 0x40007f03f803e03e 0xa0003f81fc01f01f

def z1058 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0x307f9b3cd8000000 0x183fcd9e6c000000

def z1059 : W := mkw 0xa03859a2c70b3530 0xd01c2cd163859a98 0xdff878e3c71fff39 0xeffc3c71e38fff9c

def z1060 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x0a7860c307019f18 0x053c30618380cf8c

def z1061 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfffffffffce198d9 0xfffffffffe70cc6c

def z1062 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0x1a7ffbefdce19818 0x0d3ffdf7ee70cc0c

def z1063 : W := mkw 0x005580f800200880 0x002ac07c00100440 0xffff9ffcfce278e7 0xffffcffe7e713c73

def z1064 : W := mkw 0xd0dd80fd26b41ecc 0x686ec07e935a0f66 0xffffe0ff27ff9fff 0xfffff07f93ffcfff

def z1065 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x000000dc000018c0 0x0000006e00000c60

def z1066 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdef87ce3e703ff3f 0xef7c3e71f381ff9f

def z1067 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfef8f8ffc7039f39 0xff7c7c7fe381cf9c

def z1068 : W := mkw 0x216eff0047dbe121 0x90b77f8023edf090 0x7fffff0007ffe721 0x3fffff8003fff390

def z1069 : W := mkw 0xa03859a2c70b3530 0xd01c2cd163859a98 0xfff8fff3e71fffff 0xfffc7ff9f38fffff

def z1070 : W := mkw 0x004c800006900000 0x0026400003480000 0x0b7f000007fc0001 0x05bf800003fe0000

def z1071 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfdfffffff80000c1 0xfefffffffc000060

def z1072 : W := mkw 0x016ef70006d9e001 0x80b77b80036cf000 0x217f870000fc6000 0x10bfc380007e3000

def z1073 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffffc007fff801 0x7fffffe003fffc00

def z1074 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x7f7ffb0007ff8001 0x3fbffd8003ffc000

def z1075 : W := mkw 0x100224000060c88d 0x0801120000306446 0xef8764c304e3f8ff 0xf7c3b2618271fc7f

def z1076 : W := mkw 0x116eff03b7dbe00d 0x88b77f81dbedf006 0x7f7fff03ffffe03f 0xbfbfff81fffff01f

def z1077 : W := mkw 0xc09900fc06241ec0 0x604c807e03120f60 0x828000fc07001fc1 0x4140007e03800fe0

def z1078 : W := mkw 0x801800a006001400 0x400c005003000a00 0x9ef860e307019f19 0x4f7c30718380cf8c

def z1079 : W := mkw 0x0066f603b0000000 0x00337b01d8000000 0xfc7fff3ff8000000 0xfe3fff9ffc000000

def z1080 : W := mkw 0x58c7a55d28fceacf 0xac63d2ae947e7567 0x2107871c38fc60c6 0x1083c38e1c7e3063

def z1081 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x0a7f600007fd8000 0x053fb00003fec000

def z1082 : W := mkw 0x803850a286011410 0x401c285143008a08 0x8af860e304019f18 0x457c30718200cf8c

def z1083 : W := mkw 0xa01808a047031530 0x500c045023818a98 0xdef860e307039f39 0xef7c30718381cf9c

def z1084 : W := mkw 0x004c800006900000 0x0026400003480000 0x2b7f800004fc0000 0x15bfc000027e0000

def z1085 : W := mkw 0xa13859a2c79b3530 0xd09c2cd163cd9a98 0xdef878e3c71f9f39 0xef7c3c71e38fcf9c

def z1086 : W := mkw 0x203058a2c1020120 0x10182c5160810090 0xdef878e3c7039f39 0xef7c3c71e381cf9c

def z1087 : W := mkw 0x000224000040c001 0x0001120000206000 0xef8764d324e3f8ff 0xf7c3b2699271fc7f

def z1088 : W := mkw 0xf81100f7e8241ffe 0x7c08807bf4120fff 0x808000fff8001ffe 0xc040007ffc000fff

def z1089 : W := mkw 0xf80b2d556f6fffff 0xfc0596aab7b7ffff 0xef8764d327ffffff 0xf7c3b26993ffffff

def z1090 : W := mkw 0xe8fcd9aecf9f3772 0xf47e6cd767cf9bb9 0x10789b2cdb1c0700 0x083c4d966d8e0380

def z1091 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xcaf878e3c4039f38 0xe57c3c71e201cf9c

def z1092 : W := mkw 0xe88809044fbf3ff2 0xf444048227df9ff9 0x0380000007ffffff 0x01c0000003ffffff

def z1093 : W := mkw 0xe80809044f0e3762 0xf404048227871bb1 0x03800000071e7fe7 0x01c00000038f3ff3

def z1094 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xfff87ce3c703ff39 0xfffc3e71e381ff9c

def z1095 : W := mkw 0x803858a007031400 0x401c2c5003818a00 0xdef878e307039f39 0xef7c3c718381cf9c

def z1096 : W := mkw 0x48000104080c2242 0xa400008204061121 0xf5809f3cfb1c67c7 0xfac04f9e7d8e33e3

def z1097 : W := mkw 0xe97cdba6cf9f3772 0xf4be6dd367cf9bb9 0x10789b2cdb1c0700 0x083c4d966d8e0380

def z1098 : W := mkw 0x805d80f806901400 0x402ec07c03480a00 0xbfff80fc07fc1f01 0x5fffc07e03fe0f80

def z1099 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xff879f3cfffe67e7 0xffc3cf9e7fff33f3

def z1100 : W := mkw 0x29227f02c94be133 0x94913f8164a5f099 0x40007f03f803e03e 0xa0003f81fc01f01f

def z1101 : W := mkw 0x014ea70006d8e001 0x80a75380036c7000 0x2b7f870004fc6000 0x15bfc380027e3000

def z1102 : W := mkw 0x29227f00494be123 0x94913f8024a5f091 0x40007f000003e026 0x20003f800001f013

def z1103 : W := mkw 0x80dd80f806b01c80 0x406ec07c03580e40 0xbfff80e007fc1f01 0x5fffc07003fe0f80

def z1104 : W := mkw 0x0077f6fbb040c001 0x003bfb7dd8206000 0xfc7ffffff803e000 0xfe3ffffffc01f000

def z1105 : W := mkw 0x006cd00006900000 0x0036680003480000 0x7f7ff80007fc0001 0x3fbffc0003fe0000

def z1106 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x3f7f80ec07fc1f01 0x1fbfc07603fe0f80

def z1107 : W := mkw 0x0077f6fbb0010010 0x003bfb7dd8008008 0xfc7ffffff8018018 0xfe3ffffffc00c00c

def z1108 : W := mkw 0xe88909544fbe3fe2 0xf44484aa27df1ff1 0xef8704d027fe7fe7 0xf7c3826813ff3ff3

def z1109 : W := mkw 0x0166f70000d8e001 0x80b37b80006c7000 0x297fe70000fc6000 0x14bff380007e3000

def z1110 : W := mkw 0x003050a280000000 0x0018285140000000 0xdc78fbefd8000000 0xee3c7df7ec000000

def z1111 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfffffffffc03f8ff 0xfffffffffe01fc7f

def z1112 : W := mkw 0x016eff0817dbe001 0x80b77f840bedf000 0x7f7fff0c1fffe001 0x3fbfff860ffff000

def z1113 : W := mkw 0xa16eff02c7dbf531 0xd0b77f8163edfa98 0x7fffff03c7ffff39 0xbfffff81e3ffff9c

def z1114 : W := mkw 0x805d80f006b01c80 0x402ec07803580e40 0xbfff80f007fc1fc1 0x5fffc07803fe0fe0

def z1115 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xff7ffffffce00001 0xffbffffffe700000

def z1116 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x3c7f9b2cd8000000 0x1e3fcd966c000000

def z1117 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffffe4ff27ffffff 0xfffff27f93ffffff

def z1118 : W := mkw 0x5947a75528fceacf 0xaca3d3aa947e7567 0x2107871c38fc60c6 0x1083c38e1c7e3063

def z1119 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x75009f3cfb1e67c7 0x3a804f9e7d8f33e3

def z1120 : W := mkw 0x690809044fdfe363 0xb484048227eff1b1 0x0300000007ffe701 0x0180000003fff380

def z1121 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xde7878e3c7019f18 0xef3c3c71e380cf8c

def z1122 : W := mkw 0x100324512060c88d 0x0801922890306446 0xff87e4ff24e3f8ff 0xffc3f27f9271fc7f

def z1123 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xf5009f3cfb1c67c6 0xfa804f9e7d8e33e3

def z1124 : W := mkw 0x005480a800000000 0x002a405400000000 0xf4789f3cf8000000 0xfa3c4f9e7c000000

def z1125 : W := mkw 0x803858a287031410 0x401c2c5143818a08 0xdef878e307039f19 0x6f7c3c718381cf8c

def z1126 : W := mkw 0x014ea70006d8e001 0x80a75380036c7000 0x7f7fe70007ffe001 0x3fbff38003fff000

def z1127 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x8bff00fc07fc1fc1 0x45ff807e03fe0fe0

def z1128 : W := mkw 0x0177f6fbb041c001 0x00bbfb7dd820e000 0xfc7ffffff8018000 0xfe3ffffffc00c000

def z1129 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfefffffffce39839 0xff7ffffffe71cc1c

def z1130 : W := mkw 0xc0cc800406b41ec0 0x60664002035a0f60 0xbfff803c07fc1fc1 0x5fffc01e03fe0fe0

def z1131 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff80ff07fc1ff9 0xdfffc07f83fe0ffc

def z1132 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff2cdfffe001 0x3fbfff966ffff000

def z1133 : W := mkw 0x8077f6fbb0001400 0x403bfb7dd8000a00 0xfcfffffff8001f00 0xfe7ffffffc000f80

def z1134 : W := mkw 0x2028580047030120 0x10142c0023818090 0xdef878e3c7039f39 0xef7c3c71e381cf9c

def z1135 : W := mkw 0x0076f6abb0000000 0x003b7b55d8000000 0xdc78ffeff8000000 0xee3c7ff7fc000000

def z1136 : W := mkw 0x100324512060c88d 0x0801922890306446 0x6f8764c304e3f8ff 0x37c3b2618271fc7f

def z1137 : W := mkw 0x005480a800000000 0x002a405400000000 0x10789b2cd8000000 0x083c4d966c000000

def z1138 : W := mkw 0x284c89004f9a2122 0x9426448027cd1091 0x7f7f9f00fffe6027 0xbfbfcf807fff3013

def z1139 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff1027ffe0c7 0x3fbfff8813fff063

def z1140 : W := mkw 0x21227f02c14be131 0x90913f8160a5f098 0x40007f00c003e000 0x20003f806001f000

def z1141 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff84fc27fc1fc1 0xffffc27e13fe0fe0

def z1142 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x7c7fff3cf8000000 0x3e3fff9e7c000000

def z1143 : W := mkw 0x002a7d00074be001 0x80153e8003a5f000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z1144 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff87fc3ffc1fc1 0x5fffc3fe1ffe0fe0

def z1145 : W := mkw 0xc0dd80fe86b41ed0 0x606ec07f435a0f68 0xbfff80ff07fc1fd9 0x5fffc07f83fe0fec

def z1146 : W := mkw 0xc0cd805c06b41ec0 0x6066c02e035a0f60 0x3fff801c07fc1fc1 0x1fffc00e03fe0fe0

def z1147 : W := mkw 0x0077f6fbb040c001 0x003bfb7dd8206000 0xfffffffffce3f839 0xfffffffffe71fc1c

def z1148 : W := mkw 0x204c880047920120 0x1026440023c90090 0xffff9820c7fe0721 0xffffcc1063ff0390

def z1149 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff0307ffe039 0xbfbfff8183fff01c

def z1150 : W := mkw 0x296eff004fdbe123 0x94b77f8027edf091 0xffffff10ffffe0e7 0xffffff887ffff073

def z1151 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdef87fe3ff039f39 0xef7c3ff1ff81cf9c

def z1152 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xb07f9ffff8000000 0xd83fcffffc000000

def z1153 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xbc7ffbffd8000000 0x5e3ffdffec000000

def z1154 : W := mkw 0xa03850a2c6011530 0x501c285163008a98 0x0af860c304019f38 0x057c30618200cf9c

def z1155 : W := mkw 0x004c800006900000 0x0026400003480000 0xffffe0c307ff9839 0xfffff06183ffcc1c

def z1156 : W := mkw 0x100324512060c88d 0x0801922890306446 0x8b8760d324e3f8ff 0xc5c3b0699271fc7f

def z1157 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfdfffffff8e260e7 0xfefffffffc713073

def z1158 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7fffff0007ffe0e7 0x3fffff8003fff073

def z1159 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xff7ffffffce3e0c7 0xffbffffffe71f063

def z1160 : W := mkw 0xa0385aa2d7031530 0x501c2d516b818a98 0xdef87be3df039f39 0xef7c3df1ef81cf9c

def z1161 : W := mkw 0x0146a70000d8e001 0x80a35380006c7000 0x3d7f870000fc6000 0x1ebfc380007e3000

def z1162 : W := mkw 0x006cd80007930000 0x00366c0003c98000 0x3f7f980007fc0001 0x1fbfcc0003fe0000

def z1163 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffffe0fc07ff9fc1 0x7ffff07e03ffcfe0

def z1164 : W := mkw 0x405580fc00240ac0 0x202ac07e00120560 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z1165 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0xa58000fc00001fc1 0x52c0007e00000fe0

def z1166 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xb5809f3cfb1c67c7 0x5ac04f9e7d8e33e3

def z1167 : W := mkw 0xa83859a2cf0b3532 0xd41c2cd167859a99 0xdef87be3df039f39 0xef7c3df1ef81cf9c

def z1168 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x5078fb2fd8000000 0xa83c7d97ec000000

def z1169 : W := mkw 0x790b2d556fffebef 0xbc8596aab7fff5f7 0xef8764d327ffffff 0xf7c3b26993ffffff

def z1170 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x808000fc20001fe6 0xc040007e10000ff3

def z1171 : W := mkw 0x296eff02cfdbe133 0x94b77f8167edf099 0x7f7fff03ffffe03f 0xbfbfff81fffff01f

def z1172 : W := mkw 0x016eff0127dbe001 0x80b77f8093edf000 0x7f7fff0327ffe001 0xbfbfff8193fff000

def z1173 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x9aff80fc07fc1fc0 0x4d7fc07e03fe0fe0

def z1174 : W := mkw 0x0067f65930000000 0x0033fb2c98000000 0xfc7fff3cf8000000 0xfe3fff9e7c000000

def z1175 : W := mkw 0x016ef70006d9e001 0x80b77b80036cf000 0x3f7fe70007fde001 0x1fbff38003fef000

def z1176 : W := mkw 0x014ea60006d0c001 0x00a7530003686000 0x3f7f800007fc0001 0x1fbfc00003fe0000

def z1177 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x7f7fe40007ffe001 0x3fbff20003fff000

def z1178 : W := mkw 0x004c800006900000 0x0026400003480000 0xff7f9f3cfffc0001 0xffbfcf9e7ffe0000

def z1179 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x9fff00e007fc1fc1 0x4fff807003fe0fe0

def z1180 : W := mkw 0xc01900f406241ec0 0x600c807a03120f60 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z1181 : W := mkw 0x0077f6fbb0200880 0x003bfb7dd8100440 0xfe7ffffffce01800 0xff3ffffffe700c00

def z1182 : W := mkw 0xe80809044f0f3772 0xf404048227879bb9 0x00000000031c0700 0x00000000018e0380

def z1183 : W := mkw 0x0077f6fbb040c001 0x003bfb7dd8206000 0xfffffffffce3e0e7 0xfffffffffe71f073

def z1184 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0xce8060ff04039ff9 0xe740307f8201cffc

def z1185 : W := mkw 0xe80809044f0f3772 0xf404048227879bb9 0x02800000071f9f39 0x01400000038fcf9c

def z1186 : W := mkw 0xa028580047031530 0x50142c0023818a98 0xdef878c307039f39 0xef7c3c618381cf9c

def z1187 : W := mkw 0x0075d2fbb0000000 0x003ae97dd8000000 0x10789b3cf8000000 0x083c4d9e7c000000

def z1188 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfcfffffffb000701 0xfe7ffffffd800380

def z1189 : W := mkw 0x29227f03f94be123 0x94913f81fca5f091 0x40007f03f803e026 0xa0003f81fc01f013

def z1190 : W := mkw 0xe0b158fec1271ff0 0x7058ac7f60938ff8 0xc08078ffc0039ff8 0xe0403c7fe001cffc

def z1191 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3f7fe00007ffe001 0x1fbff00003fff000

def z1192 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x9ef860e307039f39 0x4f7c30718381cf9c

def z1193 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x6b7fff0004ffe000 0x35bfff80027ff000

def z1194 : W := mkw 0xc09900f406b41ec0 0x604c807a035a0f60 0xbfff00f007fc1fc1 0x5fff807803fe0fe0

def z1195 : W := mkw 0x216eff0047dbe121 0x90b77f8023edf090 0xffffff3cffffe721 0xffffff9e7ffff390

def z1196 : W := mkw 0xa03859a2c70b3530 0xd01c2cd163859a98 0xfff8ffffff1fff39 0xfffc7fffff8fff9c

def z1197 : W := mkw 0xe89100fff8241fe2 0x7448807ffc120ff1 0x808000fff8001fe6 0xc040007ffc000ff3

def z1198 : W := mkw 0x804c800006901400 0x4026400003480a00 0x3fff800007fc1f01 0x1fffc00003fe0f80

def z1199 : W := mkw 0x1077f6fbb040c00d 0x083bfb7dd8206006 0xfefffffffc03f83f 0xff7ffffffe01fc1f

def z1200 : W := mkw 0x0066f60000900000 0x00337b0000480000 0x7d7fff0000fc0000 0x3ebfff80007e0000

def z1201 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x31809f3cfb1e67e7 0x18c04f9e7d8f33f3

def z1202 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfe7ffffffc038001 0xff3ffffffe01c000

def z1203 : W := mkw 0x0076f6aa90000000 0x003b7b5548000000 0x5078ff2cd8000000 0x283c7f966c000000

def z1204 : W := mkw 0x003374f3a0000000 0x0019ba79d0000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1205 : W := mkw 0xa83859a2cf0b3532 0xd41c2cd167859a99 0xfff87ff3ff03ffff 0xfffc3ff9ff81ffff

def z1206 : W := mkw 0x016eff0297dbe001 0x80b77f814bedf000 0x7f7fff00dfffe001 0x3fbfff806ffff000

def z1207 : W := mkw 0x0075d0fa80000000 0x003ae87d40000000 0xfc7ffffff8000000 0xfe3ffffffc000000

def z1208 : W := mkw 0x004c810006982000 0x80264080034c1000 0x3f7f870007fc6001 0x1fbfc38003fe3000

def z1209 : W := mkw 0x096eff000fdbe003 0x84b77f8007edf001 0x7f7fff003fffe007 0x3fbfff801ffff003

def z1210 : W := mkw 0x014c810006d8e001 0x80a64080036c7000 0x3f7f800007fc6001 0x1fbfc00003fe3000

def z1211 : W := mkw 0xe09908fc47271ff0 0x704c847e23938ff8 0x828000fc07039ff9 0x4140007e0381cffc

def z1212 : W := mkw 0x004c800006900000 0x0026400003480000 0xbf7f803c07fc0001 0x5fbfc01e03fe0000

def z1213 : W := mkw 0x006cd900079b2000 0x80366c8003cd9000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z1214 : W := mkw 0x404d805406b40ac0 0x2026c02a035a0560 0xbfff80fc07fc1fc1 0x5fffc07e03fe0fe0

def z1215 : W := mkw 0xa83859a2cf0b3532 0xd41c2cd167859a99 0xfef8ffffff03ff3f 0xff7c7fffff81ff9f

def z1216 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xdc7ffbefd8000000 0xee3ffdf7ec000000

def z1217 : W := mkw 0x1077f6fbb040c00d 0x083bfb7dd8206006 0xfdfffffff803e0ff 0xfefffffffc01f07f

def z1218 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdef878ffff039f39 0xef7c3c7fff81cf9c

def z1219 : W := mkw 0x216eff0047dbe121 0x90b77f8023edf090 0x7f7fff20c7ffe701 0x3fbfff9063fff380

def z1220 : W := mkw 0x016cdb0007dbe001 0x80b66d8003edf000 0x3f7f9b0007ffe001 0x1fbfcd8003fff000

def z1221 : W := mkw 0xc09100fc00241ec0 0x6048807e00120f60 0x008000c000001fc0 0x0040006000000fe0

def z1222 : W := mkw 0x016ef70006d9e001 0x80b77b80036cf000 0x0b7f600004fde000 0x05bfb000027ef000

def z1223 : W := mkw 0x004ea40006900000 0x0027520003480000 0x7f7fe40007fc0001 0x3fbff20003fe0000

def z1224 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0x71009f3cfb1e67e6 0xb8804f9e7d8f33f3

def z1225 : W := mkw 0x016ef60006d1c001 0x00b77b000368e000 0x7f7fff0007fd8001 0x3fbfff8003fec000

def z1226 : W := mkw 0x1077f6fbb020088c 0x083bfb7dd8100446 0xfefffffffc0398ff 0xff7ffffffe01cc7f

def z1227 : W := mkw 0x116eff0127dbe00d 0x88b77f8093edf006 0xffffff1327ffe0ff 0xffffff8993fff07f

def z1228 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x4b7f7f0007ffe001 0x25bfbf8003fff000

def z1229 : W := mkw 0x409100fc00240ac0 0x2048807e00120560 0x800000fc000000c0 0x4000007e00000060

def z1230 : W := mkw 0xc0dd80ffb6b41ec0 0x606ec07fdb5a0f60 0xffff9ffffffc1fc1 0xffffcffffffe0fe0

def z1231 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fff3c07ffe001 0x7fbfff9e03fff000

def z1232 : W := mkw 0xa01800a2c6001530 0x500c005163000a98 0xdef860e3c7039f39 0xef7c3071e381cf9c

def z1233 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff98fcc7fc1fc1 0xffffcc7e63fe0fe0

def z1234 : W := mkw 0x404c800406940240 0x20264002034a0120 0x3fff800007fc07c1 0x1fffc00003fe03e0

def z1235 : W := mkw 0x0044800000900000 0x0022400000480000 0x3d7f800000fc0000 0x1ebfc000007e0000

def z1236 : W := mkw 0x0166ff0001dbe001 0x80b37f8000edf000 0x7d7fff0000ffe000 0x3ebfff80007ff000

def z1237 : W := mkw 0x1077f6fbb060c88d 0x083bfb7dd8306446 0xfefffffffce198fe 0xff7ffffffe70cc7f

def z1238 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0xfc7f9ffcf8000000 0xfe3fcffe7c000000

def z1239 : W := mkw 0xe80809044f0f3772 0xf404048227879bb9 0xef8064d3271fffff 0xf7c03269938fffff

def z1240 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xffff80fc07fe1fe1 0xffffc07e03ff0ff0

def z1241 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x707fff3ff8000000 0xb83fff9ffc000000

def z1242 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x3f7ffb0007fd8001 0x1fbffd8003fec000

def z1243 : W := mkw 0x006ef60006d0c001 0x00377b0003686000 0x7f7fff0007ffe001 0x3fbfff8003fff000

def z1244 : W := mkw 0xc0dc80ac06941640 0x606e4056034a0b20 0xbfff803c07fc07c1 0x5fffc01e03fe03e0

def z1245 : W := mkw 0xe09108fc41261fe0 0x7048847e20930ff0 0xd48018fcc3021fe1 0xea400c7e61810ff0

def z1246 : W := mkw 0x1057a4f92060c88d 0x082bd27c90306446 0xfffffffffce3f8ff 0xfffffffffe71fc7f

def z1247 : W := mkw 0x116eff0007dbe00d 0x88b77f8003edf006 0x7f7fff0007ffe03f 0x3fbfff8003fff01f

def z1248 : W := mkw 0x0075d2fa90000000 0x003ae97d48000000 0x187f9becd8000000 0x0c3fcdf66c000000

def z1249 : W := mkw 0x016efe0007d3c001 0x00b77f0003e9e000 0x7f7ff80007ff8001 0x3fbffc0003ffc000

def z1250 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x987ffbfff8000000 0xcc3ffdfffc000000

def z1251 : W := mkw 0x100324512060c88d 0x0801922890306446 0xcf8760c304e3f8ff 0xe7c3b0618271fc7f

def z1252 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffff1007ffe0c1 0x7fffff8803fff060

def z1253 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xffffffd327fff8ff 0xffffffe993fffc7f

def z1254 : W := mkw 0x816eff0007dbf411 0xc0b77f8003edfa08 0x7f7fff0007fff819 0x3fbfff8003fffc0c

def z1255 : W := mkw 0x004ea40006d0c001 0x0027520003686000 0x3f7f840007fc6001 0x1fbfc20003fe3000

def z1256 : W := mkw 0xa1385ba2c70b3530 0xd09c2dd163859a98 0xdef87be3c7039f39 0xef7c3df1e381cf9c

def z1257 : W := mkw 0x004ea40006d0c001 0x0027520003686000 0x3f7fe00007fd8001 0x1fbff00003fec000

def z1258 : W := mkw 0xa03850a2c6011530 0x501c285163008a98 0xdef878e3c4019f38 0xef7c3c71e200cf9c

def z1259 : W := mkw 0x1075d2fbb020088c 0x083ae97dd8100446 0x90f89bfff80018fe 0xc87c4dfffc000c7f

def z1260 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7d7fff0003fc6000 0x3ebfff8001fe3000

def z1261 : W := mkw 0x0076f6aa90000000 0x003b7b5548000000 0x307f9f2cd8000000 0x183fcf966c000000

def z1262 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xfc78fffff8000000 0xfe3c7ffffc000000

def z1263 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x7f7f9f0007fe6001 0x3fbfcf8003ff3000

def z1264 : W := mkw 0x006efc0007d3c001 0x00377e0003e9e000 0x7f7ffc0007ffe001 0x3fbffe0003fff000

def z1265 : W := mkw 0x0077f6fbb060c881 0x003bfb7dd8306440 0xfffffffffce3f8c1 0xfffffffffe71fc60

def z1266 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0xdff878e3c703ffff 0xeffc3c71e381ffff

def z1267 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xb5ff803c03fc07c1 0x5affc01e01fe03e0

def z1268 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0x687fffdff8000000 0xb43fffeffc000000

def z1269 : W := mkw 0x68000904490e2362 0xb4000482248711b1 0xb1809f3cfb1c67e6 0xd8c04f9e7d8e33f3

def z1270 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xb1ff80fc03fc1fc0 0x58ffc07e01fe0fe0

def z1271 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0x1878fbefd8000000 0x0c3c7df7ec000000

def z1272 : W := mkw 0xc0b376ffb0241ec0 0x6059bb7fd8120f60 0xc0807ffff8001fc0 0xe0403ffffc000fe0

def z1273 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x9af878e3c7019f38 0xcd7c3c71e380cf9c

def z1274 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0xbfff80fc27fc1fe7 0xdfffc07e13fe0ff3

def z1275 : W := mkw 0xd0dd80fd26b41ecc 0x686ec07e935a0f66 0xbfff80ff07fc1fd9 0x5fffc07f83fe0fec

def z1276 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfc7ffffff8026026 0xfe3ffffffc013013

def z1277 : W := mkw 0x005580fbb0000000 0x002ac07dd8000000 0xfc7f9ffff8000000 0xfe3fcffffc000000

def z1278 : W := mkw 0x409100ffb0240ac0 0x2048807fd8120560 0x800000fff80000c0 0xc000007ffc000060

def z1279 : W := mkw 0xc0dd80fc06b51ed0 0x606ec07e035a8f68 0xbfff80fc07fd9fd9 0x5fffc07e03fecfec

def z1280 : W := mkw 0x006eff00079a2000 0x80377f8003cd1000 0x7f7fff0007fe6001 0x3fbfff8003ff3000

def z1281 : W := mkw 0x1077f6fbb020088c 0x083bfb7dd8100446 0xfffffffffce018ff 0xfffffffffe700c7f

def z1282 : W := mkw 0x016eff00079b2000 0x80b77f8003cd9000 0x7f7fff0007fc0001 0x3fbfff8003fe0000

def z1283 : W := mkw 0xa03858a2c7031530 0x501c2c5163818a98 0x5a7878e3c7039f38 0xad3c3c71e381cf9c

def z1284 : W := mkw 0x004c800006900000 0x0026400003480000 0x317f800003fc0000 0x18bfc00001fe0000

def z1285 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0xff7fffc307ffe001 0xffbfffe183fff000

def z1286 : W := mkw 0xa83858a2cf031532 0x541c2c5167818a99 0xdef878e3ff039f3f 0xef7c3c71ff81cf9f

def z1287 : W := mkw 0x016cd90007dbe001 0x80b66c8003edf000 0x7f7ff80007ffe001 0x3fbffc0003fff000

def z1288 : W := mkw 0x100324512060c88d 0x0801922890306446 0xff87ffd324e3f8ff 0xffc3ffe99271fc7f

def z1289 : W := mkw 0x100324512060c88d 0x0801922890306446 0xaf8760d304e3f8ff 0x57c3b0698271fc7f

def z1290 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7e7fff0007fd8000 0x3f3fff8003fec000

def z1291 : W := mkw 0x50c7a45d20f4cacd 0x2863d22e907a6566 0x2107801c00fc00c0 0x1083c00e007e0060

def z1292 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xb4789b3cd8000000 0x5a3c4d9e6c000000

def z1293 : W := mkw 0x21227f03f14be131 0x90913f81f8a5f098 0x40007f03f803e038 0xa0003f81fc01f01c

def z1294 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x33ff803c07fc1fc1 0x19ffc01e03fe0fe0

def z1295 : W := mkw 0x004c800006d0c001 0x0026400003686000 0x3f7f800007ffe001 0x1fbfc00003fff000

def z1296 : W := mkw 0xe88809044f9e3762 0xf444048227cf1bb1 0x01800000031e67e7 0x00c00000018f33f3

def z1297 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff00ffffe001 0xbfbfff807ffff000

def z1298 : W := mkw 0x0074d2aa90000000 0x003a695548000000 0xd4789b2cd8000000 0xea3c4d966c000000

def z1299 : W := mkw 0x216eff02c7dbe131 0x90b77f8163edf098 0x7f7fff00c7ffe001 0x3fbfff8063fff000

def z1300 : W := mkw 0xe89100fec8241ff2 0x7448807f64120ff9 0x808000fff8001ffe 0xc040007ffc000fff

def z1301 : W := mkw 0x016eff0007dbe001 0x80b77f8003edf000 0x7f7fff0027ffe027 0xbfbfff8013fff013

def z1302 : W := mkw 0x0066f6000040c001 0x00337b0000206000 0xffffff3cfce3e0e7 0xffffff9e7e71f073

def z1303 : W := mkw 0x0077f6fbb0000000 0x003bfb7dd8000000 0xfd7ffffff8026001 0xfebffffffc013000

def z1304 : W := mkw 0xd09100fd20241ecc 0x6848807e90120f66 0x808000ff00001fd8 0x4040007f80000fec

def z1305 : W := mkw 0x016cdb00079b2000 0x80b66d8003cd9000 0x317f9b0003fc0000 0x18bfcd8001fe0000

def z1306 : W := mkw 0x296eff004fdbe123 0x94b77f8027edf091 0x7f7fff0007ffe027 0x3fbfff8003fff013

def z1307 : W := mkw 0x100324593060c88d 0x0801922c98306446 0xef8764df3ce3f8ff 0xf7c3b26f9e71fc7f

def z1308 : W := mkw 0xc0dd80fc06b41ec0 0x606ec07e035a0f60 0x2bff80dc07fc1fc1 0x15ffc06e03fe0fe0

def z1309 : W := mkw 0x100324512060c88d 0x0801922890306446 0xef8764fffce3f8ff 0xf7c3b27ffe71fc7f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z8,z9]),(0,[z0,z3,z4,z5,z10,z6,z11]),(0,[z0,z3,z12,z4,z5,z10,z6]),(0,[z0,z2,z3,z13,z4,z6,z14]),(0,[z0,z2,z3,z12,z4,z15,z6])],[(0,[z0,z2,z3,z4,z5,z16,z6]),(0,[z2,z3,z7,z4,z17,z5,z6]),(0,[z0,z2,z3,z18,z4,z5,z6]),(0,[z0,z19,z20,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z6,z22]),(0,[z23,z0,z2,z3,z4,z5,z6])],[(0,[z24,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z25,z3,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z26]),(0,[z0,z2,z3,z4,z5,z27,z6]),(0,[z0,z2,z3,z4,z28,z5,z6])],[(0,[z29,z0,z30,z3,z4,z5,z6]),(0,[z31,z0,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z5,z33,z6]),(0,[z0,z2,z3,z4,z34,z5,z6]),(0,[z0,z2,z3,z4,z35,z5,z6]),(0,[z21,z0,z2,z3,z36,z4,z5]),(0,[z0,z37,z2,z3,z4,z38,z5]),(0,[z39,z0,z2,z4,z5,z40,z6]),(0,[z0,z2,z4,z5,z26,z6,z14]),(0,[z0,z2,z3,z41,z4,z5,z6])],[(0,[z2,z3,z7,z4,z5,z42,z6]),(0,[z0,z2,z3,z4,z43,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z44]),(0,[z0,z2,z3,z4,z5,z45,z6]),(0,[z0,z2,z46,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z47,z5,z6]),(0,[z48,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z4,z5,z49,z6]),(0,[z21,z0,z50,z3,z4,z5,z6]),(0,[z0,z2,z51,z3,z4,z5,z6])],[(0,[z52,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z53,z4,z5,z54]),(0,[z0,z2,z3,z55,z4,z5,z6])],[(0,[z56,z2,z3,z7,z4,z5,z6]),(0,[z2,z3,z7,z4,z5,z6,z57]),(1,[z0,z2,z3,z4,z5,z58]),(0,[z59,z60,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z61,z4,z5,z6]),(0,[z62,z21,z0,z3,z4,z5,z6]),(1,[z63,z2,z3,z4,z5,z6]),(0,[z64,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z4,z5,z6]),(1,[z0,z2,z3,z66,z5,z9])]],
   [[(0,[z32,z2,z3,z4,z5,z67,z6]),(0,[z0,z56,z2,z3,z4,z5,z6]),(0,[z68,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z15,z5,z6]),(0,[z0,z2,z3,z69,z4,z5,z6])],[(0,[z0,z2,z3,z70,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z72,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z73]),(0,[z0,z2,z3,z4,z38,z5,z22])],[(1,[z32,z2,z7,z4,z5,z6]),(0,[z0,z2,z3,z74,z4,z5,z6]),(0,[z0,z2,z75,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z26,z6]),(0,[z0,z3,z4,z5,z10,z6,z76]),(0,[z0,z2,z3,z77,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z78,z6]),(0,[z79,z0,z2,z3,z4,z5,z80]),(0,[z0,z2,z3,z81,z4,z5,z6]),(0,[z0,z2,z3,z4,z82,z5,z6]),(0,[z0,z56,z3,z4,z83,z5,z6]),(0,[z0,z2,z84,z3,z4,z5,z26])],[(0,[z2,z3,z7,z4,z5,z10,z6]),(0,[z0,z2,z3,z85,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z86]),(0,[z0,z2,z87,z3,z4,z5,z6]),(0,[z0,z84,z3,z4,z5,z10,z6]),(1,[z2,z3,z4,z5,z6,z88])],[(0,[z21,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z36,z89,z5,z6])],[(0,[z0,z2,z90,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z91,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z93]),(0,[z0,z2,z3,z94,z4,z5,z6]),(0,[z0,z95,z2,z3,z4,z5,z6])],[(0,[z0,z96,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z97]),(0,[z0,z3,z4,z98,z5,z10,z6]),(1,[z0,z2,z3,z4,z5,z99]),(0,[z100,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z32,z2,z3,z4,z5,z6,z101]),(0,[z21,z0,z3,z4,z5,z102,z6]),(1,[z0,z2,z3,z69,z5,z6]),(0,[z0,z2,z3,z4,z103,z5,z6]),(1,[z104,z2,z3,z4,z5,z6]),(0,[z0,z2,z105,z3,z4,z5,z6])],[(0,[z59,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z106,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z107]),(1,[z0,z3,z4,z5,z6,z108]),(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z110,z3,z36,z4,z5,z6])],[(0,[z2,z50,z3,z7,z4,z5,z6]),(0,[z32,z2,z3,z4,z89,z5,z6]),(0,[z111,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z112,z5,z6]),(0,[z39,z0,z113,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z114,z5,z6]),(0,[z0,z3,z36,z115,z4,z5,z6])],[(0,[z116,z2,z3,z7,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z83,z6]),(0,[z0,z2,z3,z4,z5,z99,z6])],[(0,[z0,z2,z3,z4,z5,z118,z6]),(0,[z0,z2,z3,z4,z119,z5,z6]),(1,[z0,z2,z3,z120,z4,z5]),(0,[z0,z2,z3,z121,z4,z6,z76]),(0,[z0,z2,z3,z122,z4,z5,z6])],[(0,[z2,z3,z7,z123,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z124,z6])],[(0,[z125,z0,z2,z3,z4,z5,z6]),(0,[z59,z0,z126,z3,z4,z5,z6]),(0,[z0,z2,z127,z3,z4,z5,z6]),(0,[z0,z128,z3,z4,z5,z10,z6]),(0,[z129,z21,z0,z3,z4,z5,z6]),(1,[z92,z0,z2,z98,z5,z6]),(0,[z0,z2,z50,z3,z130,z5,z6]),(0,[z131,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z4,z5,z9])],[(0,[z0,z2,z3,z4,z5,z6,z101]),(0,[z0,z2,z3,z4,z5,z132,z6]),(0,[z133,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z134]),(0,[z117,z0,z3,z4,z5,z54,z6]),(0,[z0,z2,z3,z4,z135,z5,z6]),(0,[z0,z136,z2,z3,z4,z5,z6])]],
   [[(0,[z52,z0,z30,z3,z4,z5,z6]),(0,[z137,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z138,z5,z6])],[(0,[z139,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z7,z4,z98,z5,z6]),(0,[z140,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z141,z6]),(0,[z0,z2,z3,z4,z89,z5,z6]),(0,[z0,z2,z3,z121,z4,z5,z6])],[(0,[z2,z3,z7,z4,z5,z142,z6]),(0,[z143,z32,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z5,z54,z6]),(0,[z32,z2,z3,z144,z4,z5,z6]),(0,[z145,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z146,z4,z5,z6]),(0,[z147,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z38,z22])],[(0,[z32,z0,z2,z7,z4,z5,z6]),(0,[z148,z149,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z150,z6]),(0,[z0,z3,z4,z15,z5,z10,z6]),(0,[z0,z2,z3,z151,z4,z5,z6]),(0,[z131,z0,z2,z4,z5,z6,z14]),(0,[z0,z2,z3,z4,z5,z26,z9]),(1,[z0,z2,z3,z36,z89,z5])],[(0,[z92,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z152,z4,z5,z6]),(0,[z0,z2,z3,z153,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z154,z6]),(0,[z21,z0,z56,z3,z4,z5,z6]),(0,[z0,z3,z155,z4,z5,z10,z6])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z2,z156,z3,z4,z5,z6]),(0,[z0,z157,z2,z3,z4,z5,z6]),(0,[z2,z84,z3,z77,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z158])],[(0,[z0,z2,z3,z4,z159,z5,z6]),(0,[z0,z2,z3,z155,z4,z15,z6]),(0,[z160,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z161,z5,z6])],[(0,[z0,z2,z3,z4,z15,z162,z6]),(0,[z0,z128,z3,z123,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z163]),(0,[z21,z0,z128,z3,z4,z5,z6]),(0,[z164,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z165,z4,z5,z6])]],
   [[(0,[z166,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z30,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z167,z5,z6]),(0,[z79,z0,z2,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z5,z6,z168]),(0,[z169,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z53,z4,z5,z6]),(1,[z21,z0,z3,z4,z5,z26]),(0,[z0,z3,z170,z4,z5,z10,z6]),(1,[z0,z2,z3,z4,z171,z6]),(1,[z2,z3,z172,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z173,z9])],[(0,[z0,z2,z3,z144,z4,z5,z6]),(0,[z174,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z175,z4,z5,z6]),(0,[z0,z2,z3,z89,z5,z6,z9])],[(0,[z176,z0,z2,z3,z4,z5,z6]),(0,[z177,z2,z3,z144,z4,z5,z6]),(0,[z0,z2,z3,z178,z4,z5,z6]),(0,[z179,z0,z2,z3,z4,z5,z6]),(1,[z21,z0,z3,z4,z5,z44]),(1,[z0,z2,z3,z4,z180,z6])],[(0,[z181,z0,z2,z3,z4,z5,z6]),(0,[z182,z0,z2,z3,z4,z5,z6]),(0,[z0,z183,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z184,z4,z5,z6]),(0,[z0,z56,z2,z3,z4,z83,z6]),(0,[z0,z37,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z98,z5,z6,z76]),(1,[z0,z2,z3,z4,z103,z6])],[(0,[z2,z3,z7,z185,z4,z5,z6]),(0,[z0,z3,z186,z4,z5,z10,z6]),(0,[z0,z2,z3,z187,z4,z5,z6])],[(0,[z188,z0,z2,z3,z4,z5,z6]),(0,[z116,z0,z128,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z22])],[(0,[z52,z30,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z80,z9])],[(0,[z189,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z17,z5,z6]),(0,[z0,z2,z3,z190,z4,z5,z6]),(0,[z21,z0,z2,z3,z191,z4,z5]),(0,[z0,z50,z3,z4,z5,z10,z6])]],
   [[(0,[z2,z3,z7,z191,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z192]),(0,[z0,z2,z3,z4,z193,z5,z6]),(0,[z79,z0,z3,z4,z5,z10,z6]),(0,[z133,z2,z3,z4,z5,z8,z6]),(0,[z39,z194,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z195,z4,z5,z6]),(0,[z0,z2,z50,z3,z4,z5,z6]),(0,[z0,z2,z4,z196,z5,z40,z6]),(1,[z0,z2,z3,z13,z4,z6])],[(0,[z0,z2,z3,z4,z5,z42,z6]),(0,[z0,z2,z197,z3,z4,z5,z6]),(0,[z0,z2,z3,z198,z4,z5,z6]),(0,[z92,z0,z2,z4,z98,z5,z6])],[(0,[z0,z2,z3,z4,z5,z199,z6]),(0,[z32,z2,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z200,z4,z5,z6])],[],[(0,[z29,z2,z3,z144,z4,z5,z6]),(0,[z32,z2,z3,z3,z4,z5,z6]),(0,[z0,z19,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z201,z6]),(0,[z0,z2,z202,z3,z4,z5,z6]),(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z204,z4,z5,z6]),(0,[z0,z2,z3,z4,z205,z5,z6])],[(0,[z2,z3,z7,z36,z4,z5,z6]),(0,[z206,z32,z2,z3,z4,z5,z6]),(0,[z60,z2,z3,z144,z4,z5,z6]),(0,[z148,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z207,z4,z5,z6]),(0,[z0,z2,z3,z186,z4,z5,z6]),(1,[z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z93]),(0,[z0,z2,z3,z208,z4,z5,z6]),(1,[z0,z110,z3,z4,z5,z6]),(1,[z0,z2,z3,z191,z121,z4])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z7,z4,z209,z5,z6]),(0,[z0,z2,z3,z210,z4,z5,z6]),(0,[z0,z211,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z162,z5,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z212]),(0,[z0,z2,z3,z4,z89,z5,z14]),(0,[z213,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z15,z5,z6,z76])]],
   [[(0,[z0,z2,z3,z4,z5,z214,z6]),(0,[z215,z21,z0,z3,z4,z5,z6])],[(0,[z59,z30,z2,z3,z4,z5,z6]),(0,[z48,z32,z2,z3,z4,z5,z6]),(0,[z216,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z209,z5,z6]),(0,[z21,z0,z217,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z218,z5,z6]),(0,[z23,z2,z3,z4,z5,z6,z9])],[(0,[z52,z32,z2,z3,z4,z5,z6]),(0,[z92,z2,z3,z7,z4,z5,z6]),(0,[z32,z2,z3,z4,z5,z6,z14]),(0,[z219,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z6])],[(0,[z0,z2,z220,z3,z4,z5,z6]),(0,[z2,z3,z7,z4,z5,z26,z6]),(0,[z2,z3,z7,z4,z5,z6,z76]),(1,[z0,z126,z3,z4,z5,z6])],[(0,[z32,z2,z221,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z222,z5,z6]),(0,[z0,z2,z3,z223,z4,z5,z6]),(0,[z0,z19,z2,z123,z4,z5,z6])],[(0,[z0,z224,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z225,z4,z5,z6]),(0,[z148,z0,z2,z123,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z6,z76]),(0,[z0,z226,z3,z4,z5,z10,z6])],[(0,[z0,z37,z2,z3,z4,z5,z80]),(0,[z0,z2,z3,z227,z4,z5,z6]),(0,[z0,z2,z3,z228,z4,z5,z6]),(0,[z0,z3,z4,z5,z54,z10,z6])],[(0,[z32,z2,z3,z4,z5,z8,z6]),(0,[z116,z0,z3,z4,z209,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z229]),(1,[z0,z3,z230,z4,z5,z6])]],
   [[(0,[z0,z2,z231,z3,z4,z5,z6]),(0,[z0,z2,z3,z232,z4,z5,z6]),(0,[z0,z56,z3,z4,z5,z10,z6]),(0,[z92,z21,z0,z3,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z38,z5]),(0,[z39,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z233,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z234,z6]),(0,[z21,z177,z0,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z6,z80]),(0,[z0,z2,z3,z4,z5,z124,z6]),(0,[z92,z0,z235,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z159,z5,z6]),(0,[z0,z2,z3,z236,z4,z5,z6]),(0,[z0,z237,z2,z3,z4,z5,z6])],[(0,[z0,z2,z238,z3,z4,z5,z6]),(0,[z0,z3,z130,z4,z5,z10,z6]),(0,[z0,z2,z217,z3,z4,z196,z6]),(0,[z239,z0,z2,z3,z4,z5,z6])],[(0,[z240,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z123,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z241]),(0,[z21,z0,z3,z4,z5,z6,z9]),(0,[z0,z2,z3,z242,z4,z5,z6]),(0,[z0,z243,z2,z3,z4,z5,z6]),(0,[z0,z244,z84,z3,z4,z5,z6]),(0,[z0,z2,z3,z66,z5,z6,z9]),(0,[z245,z0,z2,z3,z4,z5,z6])],[(0,[z246,z0,z2,z3,z4,z5,z6]),(0,[z48,z2,z3,z4,z162,z5,z6])],[(0,[z59,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z247,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z88])],[(0,[z0,z2,z3,z4,z248,z5,z6]),(0,[z0,z2,z3,z4,z5,z8,z6]),(0,[z249,z0,z3,z4,z5,z10,z6]),(0,[z137,z2,z217,z3,z4,z5,z6]),(0,[z104,z0,z2,z3,z4,z5,z6])],[(0,[z32,z2,z3,z4,z34,z5,z6]),(1,[z32,z2,z250,z4,z5,z6]),(0,[z0,z3,z251,z4,z5,z10,z6]),(0,[z0,z2,z3,z4,z5,z252,z6]),(0,[z0,z253,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z254,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z255,z4,z5,z6]),(0,[z21,z0,z3,z4,z256,z5,z6])],[(0,[z0,z2,z3,z4,z89,z5,z8]),(0,[z0,z56,z3,z123,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z257])],[(0,[z32,z2,z3,z4,z5,z6,z44]),(0,[z258,z0,z2,z3,z4,z5,z6]),(0,[z259,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z260,z4,z5,z6]),(1,[z52,z30,z3,z4,z5,z6]),(0,[z261,z0,z2,z3,z4,z5,z6]),(0,[z262,z0,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z50,z4,z5,z6])],[(0,[z32,z56,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z263]),(0,[z0,z2,z3,z264,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z265,z6]),(0,[z139,z32,z2,z3,z4,z5,z6]),(0,[z266,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z15,z102,z6]),(1,[z21,z0,z3,z191,z4,z5]),(0,[z267,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z268,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z269,z9])],[(0,[z270,z0,z2,z3,z4,z5,z6]),(0,[z0,z30,z128,z3,z4,z5,z6]),(1,[z59,z2,z3,z17,z5,z6]),(0,[z0,z2,z3,z271,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z272,z6]),(0,[z0,z2,z3,z4,z5,z273,z6])],[(0,[z29,z2,z221,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z274]),(0,[z48,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z275]),(0,[z0,z276,z2,z3,z4,z5,z6]),(0,[z0,z2,z277,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z278]),(0,[z0,z2,z3,z4,z279,z5,z6])]],
   [[(0,[z52,z2,z3,z7,z4,z5,z6]),(0,[z59,z2,z3,z4,z162,z5,z6]),(0,[z0,z2,z3,z4,z5,z280,z6]),(1,[z281,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z38,z6,z22]),(0,[z0,z282,z3,z191,z4,z5,z6])],[(0,[z2,z3,z7,z4,z196,z5,z6]),(0,[z2,z3,z7,z4,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z283]),(0,[z284,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z44]),(0,[z39,z0,z2,z3,z4,z5,z99]),(0,[z0,z2,z3,z268,z4,z5,z6])],[(0,[z52,z29,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z185,z4,z5,z6]),(0,[z60,z48,z2,z3,z4,z5,z6]),(0,[z285,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z286,z4,z5,z6]),(0,[z0,z2,z3,z4,z287,z5,z6]),(0,[z0,z2,z3,z288,z4,z5,z6]),(1,[z2,z3,z289,z4,z5,z6]),(0,[z39,z0,z2,z3,z69,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z290]),(0,[z0,z2,z3,z4,z291,z5,z6])],[(0,[z0,z2,z292,z3,z4,z5,z6]),(0,[z0,z37,z2,z3,z4,z5,z8]),(0,[z21,z0,z3,z4,z196,z5,z6]),(0,[z0,z293,z2,z3,z4,z5,z6])],[(0,[z0,z294,z3,z4,z162,z5,z6]),(0,[z62,z0,z2,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z54,z6]),(1,[z0,z2,z3,z4,z5,z93]),(1,[z131,z0,z2,z4,z5,z14])],[(0,[z0,z295,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z173])],[(0,[z0,z2,z3,z4,z5,z296,z6]),(0,[z0,z2,z3,z4,z38,z15,z6]),(0,[z0,z2,z3,z191,z4,z5,z6])],[(0,[z297,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z102,z6,z76]),(0,[z0,z2,z3,z4,z5,z298,z6]),(0,[z299,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z11])]],
   [[(0,[z2,z3,z7,z12,z4,z5,z6]),(0,[z32,z0,z2,z250,z4,z5,z6]),(0,[z0,z3,z36,z4,z5,z10,z6])],[(0,[z2,z3,z7,z4,z5,z102,z6]),(1,[z300,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z301,z4,z5,z6])],[(0,[z0,z2,z302,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z303,z5,z6]),(0,[z21,z0,z3,z12,z4,z5,z6])],[(0,[z59,z2,z3,z7,z4,z5,z6]),(0,[z304,z0,z2,z3,z4,z5,z6]),(0,[z305,z2,z20,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z6,z9]),(0,[z0,z2,z306,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z307,z6]),(0,[z308,z0,z2,z3,z4,z5,z6]),(0,[z309,z2,z3,z7,z4,z5,z6]),(0,[z117,z32,z2,z3,z4,z5,z6]),(0,[z79,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z310,z6]),(0,[z0,z2,z311,z3,z4,z5,z6]),(1,[z117,z0,z3,z4,z54,z6]),(0,[z0,z2,z3,z4,z15,z196,z6]),(0,[z0,z2,z3,z4,z312,z5,z6]),(0,[z0,z2,z3,z36,z4,z5,z6]),(0,[z0,z2,z3,z313,z4,z5,z6])],[(0,[z59,z29,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z121,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z102,z6]),(0,[z0,z2,z3,z4,z209,z5,z6]),(0,[z309,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z217,z3,z4,z5,z6])],[(0,[z139,z0,z2,z7,z4,z5,z6]),(0,[z2,z3,z314,z7,z4,z5,z6]),(0,[z315,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z316,z5,z6]),(0,[z0,z2,z3,z4,z5,z317,z6]),(0,[z21,z21,z0,z3,z4,z5,z6]),(1,[z21,z0,z3,z4,z38,z5]),(1,[z0,z2,z3,z12,z15,z6])],[(0,[z52,z0,z56,z3,z4,z5,z6]),(0,[z318,z2,z3,z7,z4,z5,z6]),(0,[z59,z0,z2,z3,z4,z132,z6]),(0,[z319,z0,z2,z3,z4,z5,z6]),(0,[z320,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z251,z4,z5,z6]),(0,[z0,z2,z3,z36,z4,z89,z5])]],
   [[(0,[z0,z30,z3,z4,z209,z5,z6]),(0,[z0,z2,z321,z3,z4,z5,z6]),(0,[z322,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z323,z4,z5,z6])],[(0,[z324,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z26,z6]),(0,[z0,z2,z3,z4,z5,z6,z76])],[(0,[z0,z2,z3,z4,z5,z6,z325]),(1,[z32,z2,z3,z4,z5,z6]),(0,[z326,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z327,z6]),(0,[z0,z2,z3,z4,z328,z5,z6]),(0,[z0,z2,z3,z4,z5,z14,z22]),(0,[z2,z3,z4,z5,z6,z88,z76]),(0,[z0,z2,z3,z4,z5,z6,z329]),(0,[z0,z330,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z331,z4,z5,z6]),(0,[z0,z2,z3,z332,z4,z5,z6])],[(0,[z0,z2,z333,z3,z4,z5,z6]),(0,[z139,z2,z3,z7,z4,z5,z6]),(0,[z2,z3,z7,z4,z38,z5,z6]),(0,[z0,z2,z334,z3,z4,z5,z6]),(0,[z129,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z37,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z335,z6]),(0,[z0,z3,z155,z208,z4,z5,z6])],[(0,[z133,z0,z2,z3,z4,z5,z6]),(0,[z133,z0,z25,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z336,z6]),(0,[z116,z21,z0,z3,z4,z5,z6]),(0,[z281,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z337,z5,z6]),(0,[z0,z3,z191,z230,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z338]),(0,[z0,z19,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z339,z4,z5,z6]),(0,[z21,z0,z3,z4,z38,z5,z6]),(0,[z0,z2,z3,z4,z340,z5,z6])],[(0,[z128,z2,z3,z7,z4,z5,z6]),(0,[z148,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z341,z4,z5,z6]),(0,[z0,z2,z3,z342,z4,z5,z6])],[(1,[z3,z7,z4,z5,z10,z6]),(0,[z32,z37,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z343,z7,z4,z5,z6]),(0,[z0,z344,z2,z3,z4,z5,z6]),(0,[z131,z281,z2,z3,z4,z5,z6])],[(0,[z32,z2,z3,z4,z5,z6,z22]),(0,[z32,z177,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z6,z80]),(0,[z345,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z38,z5,z10,z6])],[(0,[z0,z2,z346,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z347]),(1,[z23,z2,z3,z4,z5,z6])],[(0,[z348,z0,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z17,z5,z6]),(0,[z0,z19,z2,z20,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z349]),(0,[z0,z37,z2,z3,z4,z5,z10]),(0,[z0,z350,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z12,z130,z5,z6]),(0,[z0,z2,z3,z4,z351,z5,z6]),(0,[z0,z2,z3,z352,z4,z5,z6]),(0,[z0,z2,z353,z3,z4,z5,z6])],[(0,[z354,z0,z2,z3,z4,z5,z6]),(0,[z355,z0,z2,z3,z4,z5,z6]),(0,[z37,z2,z3,z7,z4,z5,z6]),(0,[z148,z0,z2,z20,z4,z5,z6]),(1,[z356,z2,z3,z4,z5,z6])],[(1,[z2,z50,z7,z4,z5,z6]),(0,[z32,z2,z50,z3,z4,z5,z6]),(0,[z0,z2,z250,z4,z98,z5,z6]),(0,[z357,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z103,z6,z14])],[(0,[z0,z2,z3,z4,z358,z5,z6]),(0,[z0,z359,z2,z3,z4,z5,z6])],[(0,[z360,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z361,z5,z6]),(0,[z148,z0,z3,z123,z4,z5,z6]),(0,[z0,z56,z19,z3,z4,z5,z6]),(1,[z0,z128,z3,z362,z5,z6]),(0,[z0,z3,z4,z5,z40,z10,z6]),(0,[z0,z2,z3,z4,z363,z5,z6])]],
   [[(0,[z364,z0,z2,z3,z4,z5,z6]),(0,[z39,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z365,z3,z4,z5,z6])],[(0,[z32,z19,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z366,z4,z5,z6]),(0,[z0,z2,z3,z4,z367,z5,z6]),(0,[z0,z368,z2,z3,z4,z5,z6]),(0,[z369,z0,z2,z3,z4,z5,z6]),(0,[z370,z0,z2,z3,z4,z5,z6])],[(0,[z117,z2,z3,z7,z4,z5,z6]),(0,[z79,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z371,z4,z5,z6]),(0,[z2,z20,z3,z372,z4,z5,z6]),(0,[z92,z0,z2,z3,z130,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z373]),(0,[z0,z2,z374,z3,z4,z5,z6]),(1,[z137,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z196,z6,z76])],[(0,[z32,z0,z2,z3,z4,z5,z6]),(0,[z375,z0,z2,z3,z4,z5,z6]),(0,[z117,z0,z3,z4,z5,z10,z6]),(0,[z376,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z377,z6])],[(1,[z2,z3,z372,z4,z5,z6])],[(0,[z59,z79,z2,z3,z4,z5,z6]),(1,[z305,z2,z3,z4,z5,z6]),(1,[z0,z3,z208,z4,z5,z6])],[(0,[z378,z0,z2,z3,z4,z5,z6]),(0,[z2,z20,z3,z7,z4,z5,z6]),(0,[z2,z3,z7,z155,z4,z5,z6]),(0,[z111,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z379,z5,z6]),(1,[z0,z2,z50,z130,z5,z6])],[(0,[z0,z2,z3,z4,z380,z5,z6]),(0,[z133,z0,z2,z3,z4,z5,z80]),(0,[z0,z3,z123,z4,z5,z54,z6]),(0,[z21,z0,z20,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z381,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z382]),(0,[z0,z2,z3,z4,z196,z5,z6]),(0,[z131,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z15,z5,z6])]],
   [[(1,[z2,z3,z7,z4,z5,z6]),(0,[z2,z3,z7,z4,z162,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z57]),(0,[z32,z2,z3,z4,z5,z102,z6]),(0,[z0,z2,z3,z383,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z384,z6]),(0,[z21,z0,z3,z155,z4,z5,z6])],[(0,[z32,z2,z3,z225,z4,z5,z6]),(0,[z0,z2,z3,z4,z385,z5,z6]),(0,[z2,z3,z144,z4,z162,z5,z6]),(0,[z0,z2,z386,z3,z4,z5,z6]),(1,[z116,z0,z3,z209,z5,z6]),(0,[z0,z2,z3,z387,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z6,z388]),(0,[z92,z0,z389,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z390]),(0,[z239,z0,z3,z4,z5,z6,z14]),(0,[z0,z2,z3,z12,z4,z6,z76])],[(0,[z391,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z162,z5,z6]),(0,[z392,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z393,z3,z4,z5,z6]),(0,[z0,z2,z3,z121,z4,z5,z14]),(1,[z0,z2,z3,z4,z394,z6])],[(0,[z177,z0,z2,z3,z4,z5,z6]),(0,[z59,z0,z2,z3,z4,z361,z6])],[(1,[z0,z2,z3,z4,z132,z6]),(0,[z0,z3,z4,z395,z5,z10,z6]),(1,[z0,z396,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z397,z5,z6])],[(0,[z31,z2,z3,z7,z4,z5,z6]),(0,[z0,z294,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z398,z4,z209,z5]),(0,[z215,z0,z2,z3,z4,z5,z6]),(0,[z0,z37,z2,z3,z66,z4,z5]),(0,[z399,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z400]),(0,[z0,z2,z401,z3,z4,z5,z6])],[(0,[z402,z0,z3,z4,z5,z6,z80]),(1,[z0,z2,z3,z4,z403,z5]),(0,[z0,z2,z3,z4,z303,z5,z6]),(0,[z404,z0,z2,z3,z4,z5,z6]),(0,[z131,z0,z2,z84,z4,z5,z6]),(0,[z0,z2,z3,z12,z4,z5,z6]),(0,[z0,z2,z3,z4,z405,z5,z6])],[(0,[z32,z2,z3,z123,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z102,z6]),(0,[z0,z2,z3,z406,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z407,z4,z5,z6]),(0,[z2,z3,z7,z4,z98,z5,z6]),(0,[z0,z2,z408,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z54,z6]),(0,[z0,z2,z3,z4,z409,z5,z6]),(0,[z0,z2,z396,z3,z4,z5,z6]),(0,[z0,z2,z3,z66,z4,z5,z9]),(0,[z0,z2,z3,z4,z5,z6,z410])],[(0,[z0,z2,z3,z4,z411,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z412]),(0,[z0,z2,z3,z343,z4,z5,z6]),(0,[z413,z0,z2,z3,z4,z5,z6]),(1,[z48,z2,z3,z4,z162,z6]),(0,[z79,z2,z3,z4,z5,z6,z80]),(1,[z169,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z4,z5,z6,z414]),(0,[z0,z2,z3,z415,z4,z5,z6]),(0,[z0,z2,z416,z3,z4,z5,z6])],[(0,[z417,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z7,z130,z4,z5,z6]),(0,[z21,z0,z3,z4,z98,z5,z6]),(0,[z0,z3,z121,z4,z5,z10,z6])],[(0,[z0,z2,z3,z4,z418,z5,z6]),(0,[z2,z3,z7,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z419,z5,z6]),(0,[z420,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z421,z3,z4,z5,z6]),(0,[z422,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z235,z3,z4,z5,z6]),(0,[z0,z2,z3,z289,z4,z5,z6]),(1,[z39,z0,z2,z4,z40,z6]),(0,[z0,z2,z3,z4,z5,z6,z423]),(0,[z0,z2,z3,z4,z5,z6,z424])],[(0,[z2,z3,z7,z4,z5,z6,z9]),(0,[z177,z0,z2,z3,z144,z5,z6]),(0,[z21,z0,z3,z130,z4,z5,z6]),(0,[z0,z37,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z425,z4,z5,z6]),(0,[z0,z2,z3,z4,z38,z6,z76]),(0,[z426,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z427,z4,z5,z6])],[(0,[z21,z0,z3,z7,z4,z5,z6]),(0,[z177,z0,z2,z3,z17,z5,z6]),(1,[z428,z2,z3,z4,z5,z6]),(0,[z2,z217,z3,z172,z4,z5,z6]),(0,[z131,z0,z2,z3,z4,z5,z26]),(0,[z429,z0,z2,z3,z4,z5,z6])],[(0,[z29,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z250,z50,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z430]),(0,[z431,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z432,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z433,z6]),(0,[z0,z2,z3,z434,z4,z5,z6])]],
   [[(1,[z21,z32,z3,z4,z5,z6]),(0,[z21,z0,z84,z3,z4,z5,z6]),(0,[z0,z3,z242,z4,z5,z10,z6]),(0,[z0,z2,z130,z4,z98,z5,z6]),(0,[z0,z2,z3,z4,z89,z5,z26]),(0,[z0,z2,z3,z121,z4,z5,z26]),(0,[z0,z2,z3,z435,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z436,z6]),(0,[z30,z2,z3,z7,z4,z5,z6]),(0,[z309,z32,z2,z3,z4,z5,z6]),(0,[z188,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z437,z6]),(0,[z438,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z38,z5,z6])],[(0,[z0,z3,z4,z5,z8,z10,z6]),(0,[z21,z0,z3,z362,z4,z5,z6]),(0,[z0,z3,z4,z196,z5,z10,z6]),(0,[z439,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z84,z4,z5,z26]),(0,[z0,z2,z3,z4,z440,z5,z6]),(1,[z0,z2,z3,z4,z441,z6])],[(0,[z0,z2,z3,z4,z5,z142,z6]),(0,[z0,z20,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z442]),(0,[z0,z2,z3,z443,z4,z5,z6])],[(0,[z0,z2,z3,z4,z444,z5,z6]),(0,[z60,z2,z3,z4,z5,z102,z6]),(0,[z133,z0,z2,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z445,z5,z6]),(0,[z446,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z447]),(0,[z0,z2,z3,z448,z4,z5,z6]),(0,[z160,z0,z3,z4,z5,z6,z22])],[(0,[z48,z0,z2,z3,z4,z162,z6]),(0,[z402,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z449,z6]),(0,[z0,z2,z3,z4,z5,z6,z450]),(0,[z0,z2,z451,z3,z4,z5,z6])],[(0,[z452,z0,z2,z3,z4,z5,z6]),(1,[z139,z2,z7,z4,z5,z6]),(0,[z0,z3,z362,z4,z5,z10,z6]),(0,[z0,z3,z4,z5,z6,z108,z14]),(0,[z0,z2,z3,z4,z5,z6,z453])],[(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z59,z0,z455,z3,z4,z5,z6]),(1,[z0,z244,z3,z4,z5,z6])]],
   [[(0,[z456,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z20,z3,z4,z5,z457]),(0,[z0,z56,z2,z3,z4,z54,z6])],[(0,[z169,z2,z3,z4,z209,z5,z6]),(0,[z0,z2,z3,z4,z458,z5,z6]),(0,[z131,z0,z3,z4,z5,z10,z6]),(0,[z0,z389,z2,z3,z4,z5,z6]),(0,[z0,z2,z459,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z460,z5,z6]),(0,[z2,z217,z3,z7,z4,z5,z6]),(0,[z2,z3,z7,z4,z5,z6,z80]),(0,[z148,z32,z2,z3,z4,z5,z6]),(1,[z32,z3,z4,z5,z10,z6]),(0,[z32,z2,z3,z191,z4,z5,z6]),(0,[z59,z0,z2,z461,z4,z5,z6]),(0,[z0,z128,z3,z362,z4,z5,z6]),(0,[z0,z2,z3,z4,z15,z83,z6]),(0,[z0,z37,z2,z3,z4,z5,z26]),(0,[z0,z2,z3,z462,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z463])],[(0,[z52,z0,z2,z3,z4,z5,z265]),(0,[z140,z2,z3,z7,z4,z5,z6]),(0,[z464,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z465,z4,z5,z6]),(0,[z0,z466,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z398,z4,z5,z6]),(0,[z0,z37,z2,z3,z36,z4,z5]),(0,[z0,z2,z3,z4,z467,z5,z6])],[(0,[z0,z2,z468,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z6,z80]),(0,[z133,z0,z3,z4,z5,z10,z6]),(0,[z0,z20,z3,z123,z4,z5,z6]),(0,[z0,z56,z128,z3,z4,z5,z6]),(0,[z0,z37,z2,z3,z4,z5,z44]),(0,[z0,z2,z3,z4,z5,z6,z469]),(1,[z0,z2,z3,z155,z6,z76])],[(0,[z0,z470,z2,z3,z4,z5,z6]),(0,[z148,z0,z19,z3,z4,z5,z6]),(0,[z471,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z472,z4,z5,z6]),(0,[z473,z0,z2,z3,z4,z5,z6]),(0,[z474,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z475,z4,z5,z6]),(0,[z0,z3,z4,z209,z5,z54,z6]),(0,[z0,z2,z3,z476,z4,z5,z6])],[(0,[z477,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z478,z4,z5,z6]),(0,[z0,z2,z3,z4,z479,z5,z6]),(1,[z402,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z480,z5,z6]),(0,[z0,z481,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z155,z4,z6,z76]),(0,[z482,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z7,z66,z4,z5,z6]),(0,[z32,z2,z3,z36,z4,z5,z6]),(1,[z0,z2,z3,z4,z361,z6]),(0,[z48,z21,z0,z3,z4,z5,z6]),(1,[z2,z3,z4,z43,z5,z6]),(0,[z0,z2,z3,z4,z483,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z484])],[(0,[z52,z21,z0,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z209,z5,z6]),(0,[z32,z2,z217,z3,z4,z5,z6]),(0,[z0,z3,z144,z4,z5,z10,z6]),(0,[z0,z2,z3,z4,z162,z6,z76]),(0,[z0,z3,z4,z5,z10,z6,z6])],[(0,[z0,z2,z3,z485,z4,z5,z6]),(0,[z2,z3,z7,z486,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z457]),(0,[z21,z0,z3,z66,z4,z5,z6]),(0,[z0,z2,z3,z487,z4,z5,z6])],[(0,[z0,z2,z488,z3,z4,z5,z6]),(0,[z0,z2,z3,z489,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z490]),(0,[z0,z2,z20,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z403,z5,z6]),(0,[z39,z0,z2,z3,z121,z4,z6])],[(0,[z299,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z491,z3,z4,z5,z6]),(0,[z39,z32,z2,z3,z4,z5,z6]),(0,[z21,z0,z250,z3,z4,z5,z6]),(0,[z59,z0,z2,z3,z4,z5,z492]),(0,[z493,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z494,z5,z6]),(1,[z0,z495,z3,z4,z5,z6]),(0,[z0,z2,z3,z172,z4,z5,z6]),(1,[z496,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z0,z2,z3,z497,z4,z5,z6])],[(0,[z32,z2,z3,z4,z5,z26,z6]),(0,[z32,z2,z3,z4,z5,z6,z76]),(0,[z0,z498,z2,z3,z4,z5,z6]),(0,[z0,z356,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z499,z6]),(0,[z500,z0,z2,z3,z4,z5,z6]),(0,[z59,z2,z3,z4,z17,z5,z6]),(0,[z0,z2,z3,z4,z162,z5,z6]),(0,[z0,z2,z3,z501,z4,z5,z6]),(0,[z0,z37,z3,z4,z5,z10,z6]),(0,[z0,z3,z191,z4,z5,z10,z6]),(0,[z39,z0,z2,z3,z4,z40,z6]),(0,[z502,z0,z2,z3,z4,z5,z6]),(0,[z0,z503,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z504,z6]),(1,[z0,z2,z3,z398,z4,z5])]],
   [[(0,[z0,z2,z461,z3,z4,z5,z6]),(0,[z0,z505,z2,z3,z4,z5,z6]),(0,[z506,z0,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z40,z6]),(0,[z0,z2,z3,z507,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z508]),(0,[z0,z2,z3,z4,z395,z5,z6]),(0,[z0,z2,z3,z4,z509,z5,z6]),(0,[z0,z244,z2,z3,z4,z5,z6])],[(1,[z0,z56,z3,z4,z83,z6]),(1,[z438,z2,z3,z4,z5,z6]),(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z511,z4,z5,z6])],[(0,[z2,z3,z432,z7,z4,z5,z6]),(0,[z32,z2,z3,z4,z5,z6,z9]),(0,[z32,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z4,z512,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z6]),(0,[z513,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z66,z5,z6])],[(0,[z2,z3,z7,z4,z83,z5,z6]),(0,[z514,z0,z2,z3,z4,z5,z6]),(0,[z59,z21,z0,z3,z4,z5,z6])],[(0,[z29,z0,z3,z4,z5,z54,z6]),(1,[z79,z2,z3,z4,z5,z80]),(0,[z0,z2,z3,z372,z4,z5,z6]),(0,[z0,z3,z4,z83,z5,z54,z6]),(0,[z309,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z515,z4,z5,z6]),(0,[z0,z2,z3,z4,z516,z5,z6]),(0,[z517,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z518,z5,z6]),(0,[z0,z56,z3,z4,z209,z5,z6]),(0,[z21,z0,z3,z4,z83,z5,z6]),(0,[z0,z2,z3,z4,z98,z5,z6]),(0,[z39,z356,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z519]),(0,[z2,z250,z3,z7,z4,z5,z6]),(0,[z21,z32,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z520,z4,z5,z6]),(0,[z0,z3,z4,z209,z5,z10,z6]),(0,[z0,z217,z3,z4,z5,z10,z6]),(0,[z92,z0,z2,z3,z4,z171,z6]),(1,[z0,z3,z4,z5,z6,z269]),(0,[z0,z2,z3,z4,z521,z5,z6])]],
   [[(0,[z148,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z522,z5,z6]),(0,[z523,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z116,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z336,z5,z6])],[(0,[z0,z2,z3,z524,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z525]),(0,[z0,z2,z3,z4,z5,z526,z6]),(0,[z0,z2,z3,z4,z5,z6,z9])],[(0,[z0,z2,z3,z527,z4,z5,z6]),(0,[z177,z0,z3,z4,z5,z10,z6]),(0,[z0,z128,z2,z3,z4,z5,z6]),(0,[z0,z528,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z529]),(1,[z0,z2,z217,z4,z196,z6]),(0,[z0,z2,z3,z121,z4,z15,z6]),(0,[z0,z2,z3,z4,z5,z6,z269])],[(0,[z139,z21,z0,z3,z4,z5,z6]),(1,[z0,z455,z3,z4,z5,z6]),(0,[z530,z21,z0,z3,z4,z5,z6]),(0,[z0,z393,z2,z3,z4,z5,z6]),(0,[z531,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z532,z4,z5,z6]),(0,[z0,z2,z84,z3,z4,z5,z6])],[(0,[z0,z2,z3,z155,z12,z5,z6])],[(0,[z0,z533,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z534])],[(0,[z0,z2,z3,z4,z535,z5,z6]),(1,[z0,z2,z461,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z536]),(0,[z79,z2,z3,z144,z4,z5,z6]),(0,[z0,z2,z3,z4,z256,z5,z6]),(0,[z0,z3,z4,z5,z10,z6,z14]),(0,[z0,z2,z3,z537,z4,z5,z6])]],
   [[(0,[z0,z2,z455,z3,z4,z5,z6]),(0,[z59,z0,z2,z3,z17,z5,z6]),(0,[z0,z2,z3,z4,z538,z5,z6]),(0,[z0,z2,z3,z539,z4,z5,z6]),(0,[z540,z0,z2,z3,z4,z5,z6]),(0,[z541,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z542]),(0,[z0,z2,z3,z543,z4,z5,z6])],[(0,[z544,z0,z2,z3,z4,z5,z6]),(0,[z2,z221,z3,z7,z4,z5,z6]),(0,[z0,z545,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z546,z5,z6])],[(0,[z39,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z314,z4,z5,z6]),(0,[z547,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z162,z5,z548,z6]),(0,[z0,z2,z3,z4,z549,z5,z6]),(0,[z0,z2,z50,z3,z98,z5,z6]),(1,[z0,z2,z3,z4,z5,z469]),(0,[z0,z2,z3,z550,z4,z5,z6]),(0,[z551,z0,z2,z3,z4,z5,z6])],[(1,[z29,z221,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z196,z5,z6]),(0,[z32,z2,z3,z4,z15,z5,z6]),(0,[z48,z0,z2,z3,z4,z102,z6]),(0,[z149,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z4,z5,z6]),(0,[z438,z2,z3,z4,z5,z6,z76])],[(0,[z0,z2,z3,z4,z5,z6,z552]),(0,[z164,z0,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z553]),(0,[z131,z496,z2,z3,z4,z5,z6]),(1,[z0,z282,z3,z4,z5,z6])],[(0,[z59,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z162,z5,z102,z6]),(0,[z148,z428,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z554,z6]),(0,[z2,z3,z4,z43,z209,z5,z6]),(0,[z0,z2,z3,z4,z555,z5,z6]),(0,[z0,z2,z3,z556,z4,z5,z6])],[(0,[z29,z0,z3,z4,z5,z10,z6]),(0,[z21,z0,z2,z3,z4,z5,z80]),(0,[z557,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z83,z5,z10,z6]),(0,[z39,z0,z396,z3,z4,z5,z6])],[(0,[z0,z2,z558,z3,z4,z5,z6]),(0,[z60,z0,z3,z4,z5,z10,z6]),(0,[z0,z37,z2,z3,z191,z4,z5]),(1,[z0,z389,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z559])]],
   [[(0,[z0,z2,z3,z560,z4,z5,z6]),(1,[z21,z3,z7,z4,z5,z6]),(0,[z2,z3,z7,z4,z89,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z80])],[(1,[z0,z2,z3,z4,z5,z492]),(0,[z0,z2,z3,z4,z5,z561,z6]),(0,[z0,z19,z128,z3,z4,z5,z6]),(0,[z0,z2,z562,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z563,z6])],[(0,[z32,z2,z3,z12,z4,z5,z6]),(0,[z0,z2,z3,z4,z564,z5,z6]),(0,[z21,z0,z3,z4,z89,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z565])],[(1,[z0,z2,z3,z4,z5,z265]),(0,[z0,z2,z3,z170,z4,z5,z6]),(0,[z117,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z171,z5,z6]),(0,[z104,z2,z84,z3,z4,z5,z6])],[(0,[z2,z84,z3,z7,z4,z5,z6]),(0,[z0,z250,z3,z4,z5,z10,z6])],[(0,[z566,z0,z2,z3,z4,z5,z6]),(0,[z131,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z567,z5,z6])],[(1,[z148,z0,z123,z4,z5,z6]),(0,[z0,z2,z3,z568,z4,z5,z6]),(0,[z0,z2,z3,z66,z4,z5,z6]),(0,[z0,z2,z3,z121,z4,z38,z5])],[(0,[z29,z0,z221,z3,z4,z5,z6]),(0,[z21,z29,z0,z3,z4,z5,z6]),(0,[z569,z0,z2,z3,z4,z5,z6]),(1,[z0,z294,z3,z4,z5,z6]),(0,[z92,z368,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z553,z6]),(0,[z0,z2,z570,z3,z4,z5,z6]),(0,[z0,z2,z3,z571,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z572,z5,z6]),(0,[z2,z3,z7,z4,z5,z54,z6]),(0,[z133,z32,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z102,z10,z6]),(0,[z0,z3,z4,z5,z150,z10,z6])],[(0,[z0,z2,z3,z573,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z574]),(0,[z0,z2,z575,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z576,z5,z6]),(1,[z21,z0,z3,z4,z5,z6]),(0,[z270,z0,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z577,z4,z5,z6]),(0,[z0,z2,z3,z66,z4,z89,z5]),(1,[z147,z0,z3,z4,z5,z6]),(0,[z0,z282,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z578,z5,z6]),(0,[z21,z0,z3,z144,z4,z5,z6]),(0,[z0,z579,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z54,z6]),(1,[z0,z235,z3,z4,z5,z6]),(0,[z147,z0,z3,z4,z5,z6,z9])],[(0,[z580,z0,z2,z3,z4,z5,z6])],[(0,[z0,z126,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z581]),(0,[z0,z2,z3,z4,z5,z6,z582]),(0,[z583,z0,z2,z3,z4,z5,z6]),(0,[z0,z584,z2,z3,z4,z5,z6]),(0,[z117,z0,z56,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z403,z5,z54])],[(0,[z32,z2,z3,z4,z38,z5,z6]),(0,[z585,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z83,z6,z76]),(0,[z0,z2,z586,z3,z4,z5,z6])],[(0,[z0,z221,z3,z4,z5,z10,z6]),(0,[z30,z2,z3,z144,z4,z5,z6]),(0,[z143,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z587,z6]),(0,[z588,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z2,z3,z144,z4,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z589,z6]),(0,[z0,z590,z2,z3,z4,z5,z6]),(0,[z0,z110,z2,z3,z4,z5,z6]),(1,[z160,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z591,z22])]],
   [[(0,[z0,z2,z3,z4,z592,z5,z6]),(0,[z32,z2,z3,z4,z444,z5,z6]),(0,[z0,z2,z593,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z17,z5,z6]),(0,[z0,z2,z3,z594,z4,z5,z6]),(0,[z422,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z388]),(0,[z92,z0,z2,z3,z4,z5,z6])],[(0,[z0,z595,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z173]),(0,[z596,z0,z2,z3,z4,z5,z6])],[(0,[z0,z30,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z597,z5,z6]),(0,[z0,z2,z598,z3,z4,z5,z6]),(0,[z0,z2,z3,z599,z4,z5,z6]),(0,[z0,z2,z3,z4,z600,z5,z6]),(0,[z0,z128,z3,z4,z5,z54,z6]),(0,[z0,z2,z3,z4,z83,z5,z6])],[(0,[z2,z3,z7,z362,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z8]),(0,[z0,z3,z123,z4,z5,z10,z6]),(0,[z0,z19,z3,z4,z209,z5,z6]),(0,[z0,z2,z3,z120,z4,z209,z5]),(0,[z68,z21,z0,z3,z4,z5,z6])],[(0,[z601,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z89,z5,z10,z6]),(0,[z0,z2,z3,z4,z5,z6,z602])],[(0,[z0,z603,z2,z3,z4,z5,z6]),(0,[z604,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z605,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z180,z6]),(0,[z606,z0,z2,z3,z4,z5,z6]),(0,[z194,z0,z2,z3,z4,z5,z6]),(0,[z0,z496,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z607,z5,z6]),(0,[z0,z2,z3,z4,z5,z608,z6])],[(0,[z609,z0,z2,z3,z4,z5,z6]),(0,[z32,z32,z2,z3,z4,z5,z6]),(0,[z375,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z33,z6]),(0,[z610,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z611]),(0,[z0,z2,z3,z4,z612,z5,z6])]],
   [[(0,[z116,z0,z2,z3,z4,z449,z6]),(1,[z21,z0,z3,z66,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z613]),(0,[z300,z2,z50,z3,z4,z5,z6]),(0,[z0,z2,z3,z12,z15,z5,z6]),(0,[z0,z2,z3,z36,z4,z394,z6])],[(0,[z59,z0,z2,z152,z4,z5,z6]),(0,[z0,z2,z3,z614,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z241,z6]),(0,[z116,z0,z2,z3,z362,z5,z6]),(0,[z92,z63,z2,z3,z4,z5,z6]),(0,[z0,z2,z84,z4,z5,z26,z6])],[(0,[z0,z2,z3,z4,z5,z615,z6])],[(0,[z131,z2,z3,z7,z4,z5,z6]),(0,[z324,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z616,z5,z6]),(0,[z0,z128,z2,z3,z362,z5,z6]),(0,[z21,z0,z3,z4,z5,z10,z6]),(0,[z249,z0,z2,z3,z4,z5,z6])],[(0,[z617,z0,z2,z3,z4,z5,z6]),(0,[z52,z0,z221,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z67,z6]),(1,[z21,z0,z3,z4,z5,z80]),(0,[z0,z2,z3,z4,z5,z6,z618]),(0,[z0,z3,z66,z4,z5,z10,z6]),(0,[z63,z0,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z38,z6])],[(0,[z0,z2,z3,z4,z619,z5,z6]),(0,[z0,z2,z3,z4,z54,z6,z76]),(0,[z0,z2,z3,z4,z15,z40,z6])],[(0,[z139,z0,z2,z250,z4,z5,z6]),(0,[z133,z2,z3,z7,z4,z5,z6]),(0,[z32,z620,z2,z3,z4,z5,z6]),(1,[z133,z2,z3,z4,z5,z8]),(0,[z0,z2,z226,z3,z4,z5,z6]),(0,[z300,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z621,z4,z5,z6])],[(0,[z32,z2,z20,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z622]),(0,[z21,z79,z0,z3,z4,z5,z6]),(1,[z21,z0,z3,z4,z5,z14]),(0,[z0,z113,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z7,z4,z5,z6,z14]),(0,[z32,z2,z3,z155,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z492,z6]),(0,[z0,z2,z3,z4,z623,z5,z6]),(0,[z0,z2,z20,z3,z4,z5,z241]),(0,[z0,z2,z3,z155,z5,z6,z76])],[(0,[z19,z2,z3,z7,z4,z5,z6]),(0,[z0,z3,z4,z17,z5,z10,z6]),(0,[z116,z0,z3,z4,z5,z10,z6]),(0,[z131,z21,z0,z3,z4,z5,z6])],[(0,[z206,z0,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z162,z5,z6]),(0,[z0,z2,z3,z624,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z6,z14]),(0,[z0,z2,z3,z4,z5,z6,z625]),(0,[z0,z2,z3,z4,z5,z6,z108])],[(0,[z2,z3,z18,z7,z4,z5,z6]),(0,[z0,z3,z7,z4,z5,z10,z6]),(0,[z626,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z217,z4,z196,z5,z6]),(0,[z0,z2,z3,z4,z5,z627,z6])],[(0,[z21,z0,z221,z3,z4,z5,z6]),(0,[z0,z2,z628,z3,z4,z5,z6]),(0,[z21,z0,z3,z123,z4,z5,z6]),(0,[z0,z2,z3,z629,z4,z5,z6])],[(0,[z2,z3,z7,z4,z5,z8,z6]),(0,[z0,z620,z2,z3,z4,z5,z6]),(0,[z48,z0,z2,z3,z4,z5,z6])],[(0,[z52,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z144,z4,z5,z8,z6]),(0,[z0,z2,z3,z4,z630,z5,z6]),(1,[z0,z19,z20,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z6,z22]),(0,[z631,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z632]),(0,[z0,z2,z3,z191,z4,z5,z22])],[(0,[z59,z177,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z633,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z8,z6]),(0,[z0,z2,z634,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z14,z9])]],
   [[(0,[z30,z2,z221,z3,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z50,z130,z4,z5,z6]),(1,[z0,z113,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z4,z441,z6]),(0,[z0,z2,z3,z4,z394,z5,z6])],[(0,[z2,z3,z7,z4,z5,z40,z6]),(0,[z0,z2,z50,z7,z4,z5,z6]),(0,[z116,z0,z2,z3,z209,z5,z6]),(0,[z0,z2,z3,z120,z4,z5,z6]),(0,[z0,z636,z2,z3,z4,z5,z6]),(1,[z2,z3,z77,z4,z5,z6])],[(0,[z29,z32,z2,z3,z4,z5,z6]),(0,[z240,z32,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z98,z5,z6]),(0,[z39,z0,z2,z3,z4,z196,z6])],[(0,[z60,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z637,z5,z6]),(0,[z0,z2,z3,z638,z4,z5,z6]),(0,[z0,z128,z2,z3,z209,z5,z6]),(0,[z639,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z640,z6]),(0,[z21,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z641,z6])],[(0,[z0,z128,z221,z3,z4,z5,z6]),(0,[z32,z2,z3,z130,z4,z5,z6]),(0,[z0,z2,z3,z4,z642,z5,z6]),(0,[z0,z2,z3,z130,z5,z6,z76])],[(0,[z0,z2,z3,z643,z4,z5,z6]),(0,[z32,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z644,z3,z4,z5,z6]),(0,[z0,z2,z3,z645,z4,z5,z6]),(0,[z179,z21,z0,z3,z4,z5,z6]),(0,[z0,z293,z3,z155,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z54,z6]),(1,[z21,z0,z3,z36,z4,z5]),(0,[z0,z2,z3,z4,z646,z5,z6]),(0,[z0,z2,z3,z4,z647,z5,z6])],[(0,[z0,z2,z3,z4,z648,z5,z6]),(0,[z2,z3,z7,z4,z47,z5,z6]),(0,[z32,z128,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z649,z4,z5,z6]),(1,[z239,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z650,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z591])]],
   [[(0,[z2,z3,z7,z4,z5,z6,z44]),(0,[z32,z2,z84,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z3,z4,z5,z10,z6,z212]),(0,[z0,z84,z3,z268,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z651]),(0,[z0,z2,z3,z121,z4,z6,z22])],[(0,[z0,z221,z3,z4,z209,z5,z6]),(0,[z59,z0,z2,z3,z4,z5,z6]),(1,[z21,z0,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z5,z26,z22])],[(0,[z309,z0,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z362,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z652,z6]),(1,[z0,z2,z3,z4,z449,z6]),(0,[z0,z2,z653,z3,z4,z5,z6]),(0,[z0,z2,z3,z654,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z6,z44]),(0,[z655,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z656,z5,z6]),(0,[z0,z2,z3,z4,z5,z441,z6]),(0,[z0,z2,z3,z191,z4,z38,z6])],[(0,[z0,z3,z4,z5,z10,z10,z6]),(0,[z0,z2,z3,z130,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z657,z6]),(0,[z0,z2,z3,z4,z658,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z591])],[(0,[z659,z0,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z180,z6]),(0,[z39,z0,z2,z3,z4,z5,z469]),(0,[z0,z2,z660,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z661])],[(0,[z177,z2,z3,z7,z4,z5,z6]),(0,[z318,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z662,z3,z4,z5,z6])],[(1,[z0,z2,z152,z4,z5,z6]),(0,[z0,z3,z123,z4,z209,z5,z6]),(0,[z21,z0,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z663,z4,z5,z6]),(0,[z0,z664,z2,z3,z4,z5,z6])],[(0,[z52,z0,z2,z3,z4,z5,z97]),(1,[z0,z3,z4,z5,z665,z6]),(0,[z0,z2,z3,z666,z4,z5,z6]),(0,[z0,z2,z3,z4,z667,z5,z6]),(0,[z21,z0,z3,z191,z4,z5,z6])]],
   [[(1,[z2,z7,z4,z98,z5,z6]),(0,[z133,z79,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z668,z5,z6])],[(0,[z530,z0,z2,z3,z4,z5,z6]),(0,[z139,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z58]),(0,[z0,z2,z3,z4,z89,z5,z80]),(0,[z0,z495,z2,z3,z4,z5,z6]),(0,[z148,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z362,z4,z5,z6]),(0,[z0,z2,z217,z3,z4,z38,z6]),(0,[z669,z0,z2,z3,z4,z5,z6])],[(0,[z59,z0,z2,z3,z144,z5,z6]),(0,[z59,z0,z2,z3,z4,z5,z58]),(1,[z0,z2,z3,z4,z5,z553])],[(0,[z670,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z665,z6]),(1,[z149,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z671,z4,z5,z6])],[(0,[z32,z2,z3,z4,z5,z6,z80]),(0,[z60,z0,z2,z3,z4,z162,z6]),(1,[z0,z3,z4,z5,z548,z6]),(0,[z0,z3,z362,z4,z209,z5,z6]),(1,[z0,z2,z3,z53,z4,z5]),(0,[z216,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z672,z4,z5,z6]),(0,[z2,z50,z3,z289,z4,z5,z6]),(0,[z0,z2,z3,z191,z121,z4,z6])],[(0,[z21,z0,z3,z36,z4,z5,z6]),(0,[z21,z0,z2,z3,z66,z4,z5])],[(0,[z2,z3,z7,z4,z119,z5,z6]),(0,[z0,z2,z3,z4,z673,z5,z6]),(1,[z194,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z674,z4,z5,z6]),(0,[z675,z0,z2,z3,z4,z5,z6])],[(0,[z0,z676,z2,z3,z4,z5,z6]),(0,[z305,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z15,z54,z6]),(0,[z0,z3,z4,z480,z5,z10,z6]),(0,[z0,z2,z3,z4,z677,z5,z6])]],
   [[(0,[z29,z2,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z548,z6]),(0,[z678,z0,z2,z3,z4,z5,z6]),(0,[z679,z0,z2,z3,z4,z5,z6]),(0,[z92,z0,z3,z4,z5,z10,z6]),(1,[z0,z3,z115,z4,z5,z6])],[(0,[z680,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z97]),(0,[z60,z2,z3,z7,z4,z5,z6]),(0,[z0,z428,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z681,z6])],[(0,[z0,z30,z3,z4,z5,z10,z6]),(0,[z500,z32,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z66,z4,z5,z6]),(0,[z133,z0,z495,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z26,z6]),(0,[z0,z2,z3,z682,z4,z5,z6])],[(0,[z2,z3,z7,z121,z4,z5,z6]),(0,[z0,z3,z4,z5,z665,z6,z80]),(1,[z0,z2,z3,z4,z5,z457]),(0,[z39,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z217,z3,z121,z4,z6]),(1,[z0,z293,z3,z4,z5,z6]),(0,[z0,z2,z3,z683,z4,z5,z6])],[(0,[z32,z2,z250,z3,z4,z5,z6]),(0,[z21,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z115,z4,z5,z6])],[(0,[z52,z0,z3,z4,z5,z54,z6]),(0,[z21,z0,z3,z121,z4,z5,z6]),(1,[z368,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z684,z5,z6]),(0,[z0,z2,z3,z4,z685,z5,z6]),(0,[z0,z2,z3,z191,z121,z4,z5])],[(0,[z21,z0,z3,z146,z4,z5,z6]),(0,[z0,z2,z217,z3,z4,z40,z6]),(0,[z0,z2,z3,z4,z5,z6,z14]),(0,[z0,z2,z3,z4,z5,z686,z6]),(0,[z687,z0,z2,z3,z4,z5,z6])],[(0,[z21,z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z688,z4,z5,z6]),(0,[z60,z21,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z689,z5,z6]),(0,[z21,z0,z3,z341,z4,z5,z6]),(0,[z0,z2,z3,z12,z98,z5,z6])]],
   [[(0,[z0,z2,z221,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z5,z40,z6]),(0,[z79,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z690,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z5,z6]),(0,[z691,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z6,z278]),(0,[z39,z0,z2,z217,z4,z5,z6]),(0,[z0,z2,z3,z692,z4,z5,z6]),(0,[z0,z2,z3,z230,z4,z5,z6])],[(1,[z21,z0,z3,z4,z5,z10])],[(0,[z315,z0,z2,z3,z4,z5,z6]),(1,[z60,z2,z3,z4,z102,z6]),(0,[z21,z0,z19,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z693,z6]),(0,[z0,z3,z4,z5,z10,z6,z44]),(0,[z0,z2,z694,z3,z4,z5,z6])],[(0,[z0,z2,z250,z3,z4,z5,z6]),(0,[z2,z3,z7,z144,z4,z5,z6]),(0,[z0,z2,z3,z486,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z695])],[(0,[z696,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z697,z3,z4,z5,z6]),(0,[z1,z2,z3,z7,z4,z5,z6]),(0,[z32,z2,z593,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z698,z5,z6])],[(0,[z699,z0,z2,z3,z4,z5,z6]),(0,[z116,z32,z2,z3,z4,z5,z6]),(1,[z177,z2,z3,z144,z5,z6]),(0,[z0,z2,z3,z4,z700,z5,z6]),(0,[z0,z2,z84,z3,z4,z5,z14])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z32,z30,z2,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z83,z5,z6]),(0,[z0,z2,z3,z701,z4,z5,z6]),(1,[z0,z25,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z702]),(1,[z0,z37,z3,z4,z5,z10]),(0,[z92,z0,z2,z3,z98,z5,z6]),(0,[z0,z2,z3,z4,z40,z6,z76]),(0,[z0,z2,z3,z4,z703,z5,z6])],[(0,[z29,z0,z56,z3,z4,z5,z6]),(0,[z704,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z7,z4,z5,z6,z22]),(0,[z0,z2,z3,z705,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z336,z6]),(0,[z0,z3,z4,z5,z504,z10,z6]),(1,[z0,z2,z3,z159,z5,z6]),(0,[z0,z2,z3,z4,z5,z40,z6]),(0,[z0,z2,z3,z706,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z59,z2,z3,z578,z5,z6]),(0,[z0,z30,z3,z398,z4,z5]),(0,[z2,z3,z7,z4,z5,z469]),(0,[z285,z2,z7,z4,z5,z6]),(0,[z21,z300,z3,z4,z5,z6]),(0,[z0,z3,z170,z5,z6,z278]),(0,[z0,z2,z3,z4,z707,z6])],[(0,[z708,z2,z3,z4,z5,z6]),(0,[z3,z7,z4,z5,z548,z6]),(0,[z21,z0,z3,z4,z5,z263]),(0,[z356,z396,z3,z4,z5,z6])],[(0,[z2,z3,z4,z162,z132,z6]),(0,[z2,z3,z709,z4,z5,z6]),(0,[z0,z710,z3,z4,z5,z6]),(0,[z0,z2,z3,z711,z4,z5])],[(0,[z0,z2,z3,z712,z5,z6]),(0,[z0,z2,z3,z331,z15,z6])],[(0,[z2,z660,z7,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z26])],[(0,[z0,z2,z3,z4,z5,z713]),(0,[z52,z0,z3,z4,z403,z5]),(0,[z3,z7,z115,z4,z5,z6]),(0,[z177,z2,z3,z225,z5,z6]),(0,[z116,z169,z3,z209,z5,z6]),(0,[z714,z2,z3,z4,z5,z6]),(0,[z147,z0,z3,z36,z4,z5])],[(0,[z32,z2,z573,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z283]),(0,[z239,z0,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z44]),(0,[z0,z3,z715,z4,z5,z6]),(0,[z0,z3,z4,z5,z716,z6])],[(0,[z0,z3,z4,z5,z10,z457]),(0,[z717,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z103,z6])],[(0,[z0,z3,z4,z5,z10,z492]),(0,[z147,z0,z3,z4,z5,z8]),(0,[z21,z0,z3,z4,z718,z6])],[(0,[z0,z2,z3,z4,z5,z719]),(0,[z2,z3,z432,z486,z5,z6]),(0,[z0,z2,z3,z4,z5,z720]),(0,[z21,z0,z3,z4,z5,z73])],[(0,[z0,z3,z4,z5,z10,z265]),(0,[z2,z3,z721,z4,z5,z6]),(0,[z160,z0,z3,z4,z5,z26])],[(0,[z2,z7,z643,z4,z5,z6]),(0,[z0,z2,z3,z722,z5,z6]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z38,z400])],[(0,[z235,z3,z7,z4,z5,z6]),(0,[z0,z724,z3,z4,z5,z6]),(0,[z438,z2,z3,z155,z6,z76])],[(0,[z2,z3,z7,z4,z132,z6]),(0,[z0,z126,z3,z4,z5,z492]),(0,[z725,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z726,z6])],[(0,[z2,z7,z4,z5,z6,z651]),(0,[z2,z3,z4,z727,z5,z6]),(0,[z728,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z729,z6])]],
   [[(0,[z21,z0,z3,z191,z121,z4]),(0,[z730,z0,z3,z4,z5,z6]),(0,[z0,z113,z3,z4,z5,z99])],[(0,[z21,z0,z3,z242,z4,z5]),(0,[z21,z0,z3,z4,z394,z6])],[(0,[z59,z2,z152,z17,z5,z6]),(0,[z0,z2,z3,z191,z4,z272])],[(0,[z0,z2,z3,z4,z731,z6]),(0,[z732,z2,z3,z4,z5,z6]),(0,[z59,z455,z3,z17,z5,z6]),(0,[z733,z2,z3,z4,z5,z6])],[(0,[z29,z708,z3,z4,z5,z6]),(0,[z0,z3,z387,z4,z54,z6])],[(0,[z0,z2,z3,z36,z5,z734])],[(0,[z0,z2,z3,z4,z735,z6]),(0,[z32,z19,z20,z4,z5,z6]),(0,[z736,z0,z3,z4,z5,z6]),(0,[z48,z3,z4,z162,z548,z6]),(0,[z0,z2,z737,z4,z5,z6])],[(0,[z0,z126,z3,z4,z5,z6]),(0,[z21,z3,z7,z4,z5,z10]),(0,[z324,z2,z3,z4,z5,z80]),(0,[z32,z2,z3,z4,z5,z738]),(0,[z32,z495,z3,z4,z5,z6]),(0,[z422,z21,z3,z4,z5,z8]),(0,[z21,z739,z3,z4,z5,z6]),(0,[z0,z3,z4,z38,z591,z22])],[(0,[z0,z3,z4,z5,z6,z740]),(0,[z0,z3,z4,z5,z10,z529])],[(0,[z0,z2,z3,z4,z5,z741]),(0,[z742,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z743])],[(0,[z21,z0,z3,z4,z5,z338]),(0,[z0,z293,z3,z4,z5,z6]),(0,[z21,z744,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z394,z5]),(0,[z0,z37,z3,z4,z5,z108]),(0,[z92,z0,z235,z98,z5,z6])],[(0,[z21,z0,z4,z5,z26,z14])],[(0,[z0,z30,z3,z4,z5,z265]),(0,[z2,z7,z674,z4,z5,z6]),(0,[z59,z294,z3,z4,z5,z6]),(0,[z745,z0,z3,z4,z5,z6]),(0,[z746,z2,z3,z4,z5,z6]),(0,[z747,z0,z3,z4,z5,z6]),(0,[z0,z748,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z749]),(0,[z19,z20,z372,z4,z5,z6]),(0,[z0,z2,z3,z750,z5,z6])],[(0,[z0,z3,z4,z418,z54,z6]),(0,[z21,z0,z3,z550,z4,z5]),(0,[z0,z3,z208,z4,z15,z6])],[(1,[z708,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z665,z97]),(0,[z0,z2,z3,z4,z5,z751]),(0,[z79,z402,z3,z4,z5,z80]),(0,[z0,z2,z3,z4,z5,z241])]],
   [[(0,[z420,z0,z123,z4,z5,z6]),(0,[z0,z56,z3,z4,z600,z6])],[(0,[z2,z3,z18,z4,z162,z6]),(0,[z300,z2,z461,z4,z5,z6]),(0,[z169,z56,z3,z4,z5,z6]),(0,[z21,z0,z3,z13,z4,z14]),(0,[z21,z0,z3,z4,z441,z6]),(0,[z0,z752,z3,z4,z5,z6])],[(0,[z32,z3,z4,z5,z6,z269]),(0,[z0,z2,z3,z4,z5,z753]),(0,[z21,z0,z3,z427,z4,z5]),(0,[z0,z2,z3,z4,z38,z469])],[(0,[z21,z0,z3,z754,z4,z5])],[(0,[z2,z3,z4,z755,z5,z6]),(0,[z0,z389,z3,z4,z5,z93]),(0,[z756,z2,z3,z4,z5,z6])],[(0,[z0,z25,z3,z4,z5,z6]),(0,[z21,z0,z3,z223,z4,z5]),(0,[z0,z37,z3,z4,z5,z10]),(0,[z0,z3,z4,z5,z757,z6]),(0,[z3,z4,z5,z10,z6,z173]),(0,[z758,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z759]),(0,[z3,z7,z4,z5,z6,z108]),(0,[z21,z0,z3,z462,z4,z5]),(0,[z760,z0,z3,z4,z5,z93]),(0,[z194,z2,z3,z4,z5,z99])],[(0,[z21,z32,z3,z4,z5,z33]),(0,[z2,z3,z761,z17,z5,z6]),(0,[z762,z2,z3,z4,z5,z6])],[(0,[z52,z620,z3,z4,z5,z6]),(0,[z0,z763,z123,z4,z5,z6]),(0,[z764,z2,z3,z4,z5,z6])],[(0,[z32,z765,z3,z4,z5,z6]),(0,[z305,z19,z20,z4,z5,z6]),(1,[z0,z2,z3,z766,z4])],[(0,[z678,z30,z3,z4,z5,z6]),(0,[z767,z32,z3,z4,z5,z6]),(0,[z32,z2,z461,z4,z5,z6]),(0,[z59,z2,z3,z17,z5,z6]),(0,[z23,z3,z4,z5,z6,z269])],[(0,[z0,z3,z53,z230,z4,z5]),(0,[z21,z281,z3,z4,z5,z6]),(0,[z0,z768,z3,z4,z5,z6])],[(0,[z378,z2,z7,z4,z5,z6]),(0,[z281,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z769,z6]),(0,[z32,z7,z4,z5,z10,z6]),(0,[z0,z3,z770,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z749]),(0,[z771,z2,z3,z4,z5,z6]),(0,[z2,z3,z772,z4,z5,z6]),(0,[z0,z773,z3,z4,z5,z6])],[(0,[z249,z221,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z57]),(0,[z32,z2,z3,z4,z5,z469]),(0,[z0,z3,z4,z449,z10,z6]),(0,[z0,z2,z3,z121,z4,z290])],[(0,[z2,z3,z289,z4,z5,z6]),(0,[z32,z774,z3,z4,z5,z6]),(0,[z438,z2,z3,z4,z162,z6]),(0,[z775,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z93]),(0,[z0,z2,z3,z66,z5,z9])],[(0,[z0,z2,z3,z4,z5,z776]),(0,[z30,z3,z343,z4,z5,z6]),(0,[z2,z3,z7,z4,z777,z6]),(0,[z778,z2,z3,z4,z5,z6]),(0,[z0,z3,z629,z209,z5,z6])]],
   [[(0,[z2,z3,z7,z4,z5,z779]),(0,[z21,z3,z7,z4,z5,z14]),(0,[z780,z2,z3,z4,z5,z6]),(0,[z117,z0,z3,z4,z403,z5])],[(0,[z239,z0,z3,z13,z4,z6])],[(0,[z32,z389,z3,z4,z5,z6]),(0,[z0,z19,z575,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z400]),(0,[z0,z244,z84,z4,z5,z26]),(0,[z0,z2,z3,z155,z6,z781]),(0,[z147,z0,z3,z66,z4,z5])],[(0,[z60,z2,z152,z4,z5,z6]),(0,[z21,z0,z3,z663,z4,z5])],[(0,[z59,z2,z3,z673,z5,z6]),(0,[z782,z2,z3,z4,z5,z6])],[(0,[z0,z783,z3,z4,z5,z6]),(0,[z784,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z97]),(0,[z2,z50,z7,z130,z5,z6]),(0,[z0,z3,z362,z5,z6,z278]),(0,[z2,z3,z785,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z786])],[(0,[z104,z2,z3,z4,z5,z6]),(0,[z2,z3,z7,z4,z787,z6]),(0,[z788,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z159,z5,z99]),(0,[z0,z3,z4,z5,z6,z789])],[(0,[z21,z0,z3,z4,z5,z437]),(0,[z0,z2,z3,z4,z790,z6])],[(0,[z0,z2,z4,z791,z5,z6]),(0,[z2,z3,z792,z4,z5,z6])],[(0,[z32,z294,z3,z4,z5,z6]),(0,[z402,z32,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z793])],[(0,[z3,z7,z4,z794,z5,z6]),(0,[z21,z0,z3,z4,z5,z430])],[(0,[z21,z3,z144,z4,z5,z8]),(0,[z21,z0,z3,z170,z4,z5]),(0,[z2,z3,z795,z4,z5,z6])],[(0,[z21,z428,z3,z4,z5,z6]),(0,[z0,z3,z4,z83,z796,z6]),(0,[z0,z3,z159,z5,z10,z6])],[(0,[z29,z2,z152,z4,z5,z6]),(0,[z21,z3,z7,z4,z5,z26]),(0,[z21,z0,z3,z4,z336,z6]),(0,[z2,z3,z797,z4,z5,z6]),(0,[z798,z2,z3,z4,z5,z6])],[(0,[z29,z455,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z38,z15]),(0,[z2,z3,z799,z4,z5,z6])]],
   [[(0,[z21,z3,z7,z4,z5,z44]),(0,[z2,z3,z7,z4,z5,z553]),(0,[z239,z3,z7,z4,z5,z6]),(0,[z368,z2,z3,z4,z180,z6]),(0,[z0,z3,z800,z4,z5,z6]),(0,[z0,z3,z191,z230,z121,z4])],[(0,[z0,z2,z3,z4,z5,z801])],[(0,[z140,z2,z3,z47,z5,z6]),(0,[z149,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z802,z5,z6]),(0,[z21,z3,z709,z4,z5,z6]),(0,[z39,z21,z0,z3,z4,z38]),(0,[z21,z0,z3,z674,z4,z5]),(0,[z0,z3,z4,z5,z803,z6]),(0,[z0,z2,z3,z66,z5,z734])],[(0,[z0,z804,z3,z4,z5,z6]),(0,[z0,z84,z268,z4,z5,z26]),(0,[z0,z805,z3,z4,z5,z6])],[(0,[z0,z56,z3,z4,z411,z6]),(0,[z2,z3,z7,z4,z5,z806]),(0,[z315,z593,z3,z4,z5,z6]),(0,[z0,z2,z461,z4,z132,z6]),(0,[z0,z807,z3,z4,z5,z6]),(0,[z21,z63,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z808,z6]),(0,[z2,z3,z372,z4,z5,z457]),(0,[z809,z2,z3,z4,z5,z6]),(0,[z2,z3,z66,z5,z173,z9])],[(0,[z810,z0,z3,z4,z5,z6]),(0,[z21,z0,z3,z352,z4,z5]),(0,[z21,z0,z3,z4,z5,z811]),(0,[z0,z2,z3,z4,z5,z812]),(0,[z0,z813,z3,z4,z5,z6])],[(0,[z2,z3,z172,z4,z5,z6]),(0,[z294,z3,z144,z4,z5,z6]),(0,[z814,z2,z3,z4,z5,z6]),(0,[z0,z396,z3,z4,z5,z469])],[(0,[z2,z662,z7,z4,z5,z6]),(0,[z0,z2,z3,z69,z5,z99])],[(0,[z21,z0,z3,z4,z5,z469]),(0,[z0,z3,z754,z4,z5,z6]),(0,[z815,z2,z3,z4,z5,z6]),(0,[z0,z816,z3,z4,z5,z6])],[(0,[z2,z3,z144,z5,z6,z490]),(0,[z0,z3,z4,z5,z6,z817]),(0,[z0,z3,z4,z395,z6,z212])],[(0,[z0,z2,z3,z4,z5,z818]),(0,[z32,z2,z701,z4,z5,z6]),(0,[z0,z819,z3,z4,z5,z6]),(0,[z820,z0,z3,z4,z5,z553])],[(0,[z3,z7,z230,z4,z5,z6]),(0,[z0,z2,z821,z4,z5,z6]),(0,[z0,z3,z822,z4,z5,z6])],[(0,[z133,z2,z3,z4,z5,z33]),(0,[z823,z0,z3,z4,z5,z6])],[],[(0,[z139,z2,z824,z4,z5,z6]),(0,[z21,z7,z4,z98,z5,z6]),(0,[z0,z3,z120,z115,z4,z5]),(0,[z21,z0,z3,z288,z4,z5]),(0,[z0,z3,z191,z121,z4,z10])]],
   [[(0,[z2,z3,z372,z4,z5,z6]),(0,[z0,z2,z3,z825,z5,z6])],[(0,[z126,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z826,z4,z5]),(0,[z0,z3,z208,z4,z5,z6])],[(0,[z2,z3,z827,z4,z5,z6]),(0,[z0,z2,z50,z130,z5,z6])],[(0,[z828,z2,z3,z4,z5,z6]),(0,[z117,z0,z3,z4,z796,z6]),(0,[z0,z2,z829,z4,z5,z6])],[(0,[z110,z3,z7,z4,z5,z6]),(0,[z244,z3,z77,z4,z5,z6])],[(0,[z0,z3,z4,z5,z10,z6]),(0,[z50,z7,z4,z5,z10,z6]),(0,[z60,z21,z3,z4,z102,z6]),(0,[z0,z3,z4,z830,z5,z6]),(0,[z116,z0,z3,z209,z5,z6]),(0,[z0,z3,z4,z336,z10,z6]),(0,[z0,z110,z3,z4,z5,z6]),(0,[z131,z0,z2,z4,z103,z14]),(0,[z0,z3,z155,z208,z6,z76])],[(0,[z32,z2,z628,z4,z5,z6]),(0,[z21,z0,z3,z4,z132,z6]),(0,[z2,z3,z4,z5,z6,z831]),(0,[z0,z3,z66,z5,z269,z9])],[(0,[z29,z593,z3,z4,z5,z6]),(0,[z2,z3,z832,z4,z5,z6]),(0,[z21,z0,z3,z198,z4,z5])],[(0,[z0,z2,z3,z833,z4,z5]),(0,[z111,z2,z3,z225,z5,z6]),(0,[z3,z4,z5,z6,z173,z269])],[(0,[z48,z294,z3,z4,z162,z6]),(0,[z0,z2,z3,z443,z6,z76])],[(0,[z3,z7,z268,z4,z5,z6]),(0,[z32,z2,z3,z4,z38,z22]),(0,[z0,z3,z4,z5,z834,z6]),(0,[z0,z2,z3,z4,z403,z5]),(0,[z835,z2,z3,z4,z5,z6]),(0,[z356,z2,z3,z69,z5,z6]),(0,[z0,z2,z3,z4,z836,z6])],[(0,[z32,z113,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z419,z5]),(0,[z0,z2,z837,z4,z5,z6]),(0,[z0,z2,z3,z12,z340,z6])],[(0,[z2,z3,z4,z5,z6,z838]),(0,[z21,z0,z3,z122,z4,z5])],[(0,[z2,z3,z7,z4,z5,z58]),(0,[z300,z2,z250,z4,z5,z6]),(0,[z0,z455,z3,z4,z361,z6]),(0,[z839,z0,z3,z4,z5,z6])],[(0,[z2,z3,z7,z840,z4,z6]),(0,[z0,z2,z841,z4,z5,z6]),(0,[z63,z3,z4,z5,z10,z6])],[(0,[z39,z0,z2,z4,z40,z6])]],
   [[(0,[z0,z842,z3,z4,z5,z6]),(0,[z128,z3,z7,z362,z5,z6]),(0,[z21,z843,z3,z4,z5,z6]),(0,[z21,z356,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z844]),(0,[z174,z2,z7,z4,z5,z6]),(0,[z32,z2,z3,z4,z5,z713]),(0,[z2,z152,z4,z162,z5,z6]),(0,[z2,z3,z845,z4,z5,z6]),(0,[z21,z0,z3,z846,z5,z6]),(0,[z2,z3,z4,z5,z6,z847])],[(0,[z2,z3,z848,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z347]),(0,[z0,z2,z586,z4,z5,z14])],[(0,[z596,z2,z7,z4,z5,z6]),(0,[z32,z2,z3,z4,z103,z6]),(0,[z0,z2,z3,z849,z4,z6]),(0,[z2,z850,z3,z4,z5,z6])],[(0,[z21,z32,z3,z4,z5,z6]),(0,[z2,z3,z4,z162,z6,z581]),(0,[z21,z0,z3,z4,z5,z49]),(0,[z179,z0,z3,z256,z5,z6])],[(0,[z0,z2,z3,z4,z5,z851]),(0,[z356,z113,z3,z4,z5,z6])],[(0,[z32,z2,z250,z4,z5,z6]),(0,[z2,z3,z7,z69,z5,z6]),(0,[z206,z2,z3,z4,z67,z6]),(0,[z0,z2,z852,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z99])],[(0,[z21,z3,z7,z4,z5,z57]),(0,[z0,z2,z3,z4,z853,z6]),(0,[z0,z2,z854,z4,z5,z6]),(0,[z21,z0,z3,z4,z395,z5])],[(0,[z0,z2,z3,z4,z5,z855])],[(1,[z0,z3,z802,z5,z6]),(0,[z0,z3,z55,z4,z5,z10]),(1,[z21,z0,z3,z4,z394]),(0,[z92,z368,z2,z98,z5,z6])],[(0,[z21,z0,z3,z4,z5,z234]),(0,[z160,z32,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z361,z492]),(0,[z368,z2,z3,z4,z5,z93]),(0,[z0,z856,z3,z4,z5,z6])],[(0,[z0,z857,z3,z4,z5,z6]),(0,[z0,z3,z858,z4,z5,z548]),(0,[z0,z244,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z859,z6]),(0,[z2,z3,z860,z4,z5,z6])],[(0,[z2,z3,z7,z4,z5,z861]),(0,[z2,z152,z7,z4,z5,z6]),(0,[z21,z0,z3,z4,z567,z5]),(0,[z862,z2,z3,z4,z5,z6])],[(0,[z32,z2,z3,z4,z5,z553]),(0,[z2,z3,z4,z5,z6,z863]),(0,[z0,z2,z3,z4,z864,z5])],[(0,[z0,z2,z3,z4,z5,z865]),(0,[z2,z84,z7,z4,z5,z26]),(0,[z21,z866,z3,z4,z5,z6]),(0,[z0,z867,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z504,z265]),(0,[z868,z2,z3,z4,z5,z6]),(0,[z32,z2,z197,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z869]),(0,[z21,z0,z3,z4,z5,z565]),(0,[z21,z0,z3,z4,z5,z382]),(0,[z870,z2,z3,z4,z5,z6]),(0,[z871,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z7,z4,z38,z22]),(0,[z872,z0,z3,z4,z5,z6]),(0,[z0,z3,z36,z89,z5,z10]),(0,[z0,z2,z3,z155,z6,z76])],[(0,[z60,z3,z4,z102,z10,z6]),(0,[z21,z0,z3,z435,z4,z5]),(0,[z0,z873,z3,z4,z5,z6]),(0,[z0,z3,z874,z4,z5,z6])],[(0,[z0,z875,z3,z4,z5,z6]),(0,[z0,z110,z3,z36,z89,z5])],[(0,[z21,z3,z4,z5,z6,z88]),(0,[z0,z876,z3,z4,z5,z6])],[(0,[z21,z3,z7,z4,z38,z5]),(0,[z2,z3,z4,z5,z6,z173]),(0,[z877,z2,z3,z4,z5,z6])],[(0,[z2,z3,z7,z712,z5,z6]),(0,[z32,z2,z3,z4,z5,z741]),(0,[z0,z878,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z749,z6]),(0,[z879,z2,z3,z4,z5,z6])],[(0,[z29,z0,z3,z4,z403,z5]),(0,[z32,z293,z3,z4,z5,z6]),(0,[z59,z2,z3,z761,z5,z6]),(0,[z48,z2,z3,z4,z880,z6]),(0,[z0,z2,z3,z881,z4,z5])],[(0,[z0,z2,z3,z4,z882,z6]),(0,[z0,z2,z824,z4,z5,z6]),(0,[z21,z32,z3,z4,z5,z80]),(0,[z0,z2,z3,z883,z4,z5]),(0,[z21,z3,z4,z884,z5,z6]),(0,[z0,z2,z3,z159,z38,z6])],[],[(0,[z2,z3,z7,z4,z103,z6]),(0,[z0,z3,z4,z5,z757,z99])],[(0,[z0,z2,z3,z4,z5,z885])],[(0,[z52,z30,z3,z4,z5,z97]),(0,[z886,z3,z7,z4,z5,z6]),(0,[z2,z3,z7,z4,z5,z720]),(0,[z0,z3,z4,z5,z150,z241])],[(0,[z2,z3,z824,z4,z5,z6]),(0,[z0,z887,z3,z4,z5,z6]),(0,[z116,z0,z3,z209,z449,z6]),(0,[z169,z3,z4,z5,z54,z6])],[(0,[z0,z2,z152,z4,z5,z492]),(0,[z116,z0,z3,z802,z5,z6]),(0,[z0,z2,z3,z4,z796,z6]),(0,[z0,z2,z3,z556,z15,z6]),(0,[z21,z0,z3,z4,z38,z5]),(0,[z21,z0,z3,z4,z5,z388]),(0,[z0,z3,z888,z4,z5,z6]),(0,[z0,z2,z3,z12,z15,z6])],[(0,[z0,z455,z3,z4,z5,z492]),(0,[z438,z2,z3,z4,z5,z6]),(0,[z0,z56,z3,z4,z83,z6]),(0,[z194,z2,z3,z4,z5,z469]),(0,[z104,z3,z268,z4,z5,z6])],[(0,[z0,z3,z889,z4,z5,z6]),(0,[z3,z77,z268,z4,z5,z6])]],
   [[(1,[z21,z0,z3,z4,z103]),(0,[z21,z0,z3,z497,z4,z5]),(0,[z3,z172,z4,z5,z10,z6]),(0,[z0,z890,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z891]),(0,[z32,z37,z3,z4,z5,z10]),(0,[z32,z25,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z892,z6]),(0,[z596,z0,z2,z4,z5,z14])],[(0,[z32,z2,z3,z159,z5,z6]),(0,[z893,z3,z4,z5,z10,z6])],[(0,[z0,z2,z3,z4,z894,z6]),(0,[z216,z0,z75,z4,z5,z6]),(0,[z0,z2,z3,z352,z89,z5]),(0,[z160,z0,z3,z4,z38,z5])],[(0,[z2,z3,z4,z895,z5,z6])],[(0,[z2,z3,z314,z4,z5,z8]),(0,[z21,z0,z3,z230,z4,z5]),(0,[z747,z0,z3,z4,z5,z469])],[],[(0,[z0,z896,z3,z4,z5,z6]),(0,[z21,z3,z172,z4,z5,z6]),(0,[z0,z3,z4,z5,z897,z6]),(0,[z0,z217,z4,z196,z10,z6]),(0,[z0,z2,z217,z4,z196,z6])],[(0,[z2,z3,z4,z5,z749,z80]),(0,[z898,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z6,z781]),(0,[z0,z2,z3,z122,z121,z4])],[(0,[z21,z0,z461,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z553])],[(0,[z32,z2,z3,z66,z5,z9]),(0,[z32,z2,z3,z4,z5,z58]),(0,[z899,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z900,z6]),(0,[z2,z3,z144,z5,z6,z134]),(0,[z133,z495,z3,z4,z5,z8]),(0,[z744,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z629,z6,z76]),(0,[z3,z4,z901,z5,z10,z6]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z194,z396,z3,z4,z5,z6]),(0,[z0,z3,z903,z4,z5,z6])],[(0,[z2,z50,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z904,z6]),(0,[z905,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z394,z10,z6]),(0,[z356,z2,z3,z159,z5,z6])],[(0,[z0,z128,z3,z4,z449,z6])],[(0,[z0,z128,z3,z362,z5,z6]),(0,[z0,z128,z3,z645,z5,z6]),(0,[z21,z0,z2,z3,z4,z103]),(0,[z0,z37,z3,z4,z5,z811])],[(0,[z29,z221,z3,z4,z5,z6]),(0,[z116,z3,z7,z209,z5,z6]),(0,[z0,z2,z3,z906,z5,z6]),(0,[z0,z2,z3,z159,z5,z469]),(0,[z0,z2,z3,z4,z103,z22]),(0,[z0,z3,z4,z5,z6,z907])]],
   [[(0,[z0,z908,z3,z4,z5,z6]),(0,[z0,z282,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z909]),(0,[z137,z2,z3,z4,z5,z6]),(0,[z2,z386,z7,z4,z5,z6])],[(0,[z32,z2,z3,z4,z5,z97]),(0,[z23,z2,z3,z4,z5,z58]),(0,[z23,z2,z3,z66,z5,z9])],[(0,[z32,z2,z3,z69,z5,z6]),(0,[z910,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z911])],[(0,[z324,z2,z3,z4,z5,z57]),(0,[z21,z0,z3,z200,z4,z5]),(0,[z912,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z492]),(0,[z0,z3,z4,z913,z10,z6]),(0,[z0,z2,z3,z4,z5,z914]),(0,[z0,z2,z4,z5,z915,z14])],[],[(0,[z0,z2,z3,z4,z5,z265]),(0,[z500,z620,z3,z4,z5,z6]),(0,[z32,z2,z286,z4,z5,z6])],[(0,[z0,z2,z3,z4,z916,z6]),(0,[z2,z3,z7,z159,z5,z6]),(0,[z21,z0,z3,z4,z5,z589]),(0,[z0,z3,z917,z208,z4,z5])],[(0,[z0,z918,z3,z4,z5,z6])],[(0,[z148,z0,z123,z4,z5,z6]),(0,[z0,z3,z4,z5,z108,z457])],[(0,[z21,z32,z3,z4,z5,z101]),(0,[z0,z3,z123,z4,z5,z241]),(0,[z0,z2,z75,z4,z5,z26])],[(0,[z21,z149,z3,z4,z5,z6]),(0,[z0,z396,z3,z159,z5,z6])],[(0,[z2,z217,z7,z4,z196,z6]),(0,[z21,z0,z3,z210,z4,z5]),(0,[z919,z2,z3,z4,z5,z6])],[(0,[z139,z21,z7,z4,z5,z6]),(0,[z455,z3,z7,z4,z5,z6]),(0,[z0,z235,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z920,z6]),(0,[z0,z3,z802,z209,z5,z6]),(0,[z21,z0,z3,z159,z5,z6]),(0,[z0,z3,z4,z5,z6,z921]),(0,[z922,z2,z3,z4,z5,z6])],[(0,[z21,z0,z3,z4,z5,z519]),(0,[z2,z7,z4,z385,z5,z6]),(0,[z21,z0,z3,z4,z5,z652]),(0,[z0,z2,z152,z4,z361,z6]),(0,[z0,z3,z4,z5,z923,z6]),(0,[z924,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z708,z3,z4,z5,z6]),(0,[z2,z3,z7,z66,z5,z9]),(0,[z0,z495,z3,z4,z5,z8]),(0,[z0,z2,z3,z69,z5,z469])],[(0,[z21,z0,z3,z191,z4,z38])],[(0,[z0,z2,z3,z4,z5,z925]),(0,[z0,z2,z3,z4,z926,z6])],[(0,[z52,z3,z4,z5,z6,z388]),(0,[z0,z3,z4,z5,z927,z6]),(0,[z0,z3,z4,z5,z10,z93]),(0,[z928,z2,z3,z4,z5,z6])],[(0,[z21,z32,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z132,z58]),(1,[z0,z3,z4,z796,z6]),(0,[z131,z0,z4,z5,z10,z14])],[(0,[z300,z2,z50,z130,z5,z6]),(0,[z929,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z930]),(0,[z21,z0,z3,z4,z5,z58]),(0,[z21,z0,z3,z66,z5,z9]),(0,[z0,z3,z931,z4,z5,z6])],[(0,[z7,z4,z98,z5,z10,z6]),(0,[z21,z0,z3,z4,z5,z536]),(0,[z63,z235,z3,z4,z5,z6])],[(0,[z2,z3,z7,z4,z5,z97]),(0,[z300,z3,z4,z5,z10,z6]),(0,[z932,z2,z3,z4,z5,z6])],[(0,[z79,z2,z3,z4,z5,z749]),(0,[z933,z2,z3,z4,z5,z6]),(0,[z0,z2,z84,z4,z5,z26])],[(0,[z0,z2,z3,z4,z5,z934])],[(0,[z0,z2,z3,z4,z935,z6]),(0,[z0,z113,z3,z4,z5,z469])],[(0,[z2,z7,z4,z5,z6,z430]),(0,[z2,z3,z936,z4,z5,z6])],[(0,[z32,z3,z208,z4,z5,z6]),(0,[z0,z3,z937,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z938]),(0,[z0,z396,z3,z69,z5,z6]),(0,[z0,z2,z3,z121,z4,z103])],[],[(0,[z0,z2,z3,z4,z5,z939]),(0,[z21,z0,z3,z69,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z940])],[(0,[z32,z3,z4,z5,z10,z6]),(0,[z32,z110,z3,z4,z5,z6]),(0,[z0,z3,z941,z4,z5,z6]),(0,[z23,z2,z3,z4,z5,z8]),(0,[z21,z3,z289,z4,z5,z6]),(0,[z0,z2,z3,z4,z942,z6])],[(0,[z2,z7,z4,z444,z5,z6]),(0,[z943,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z944]),(0,[z866,z2,z3,z4,z5,z6]),(0,[z0,z3,z251,z209,z5,z6])],[(0,[z2,z3,z18,z4,z119,z6]),(0,[z0,z455,z152,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z526]),(0,[z0,z2,z3,z4,z103,z469]),(0,[z39,z0,z2,z4,z40,z99])],[(0,[z0,z221,z3,z398,z4,z5]),(0,[z2,z3,z945,z4,z5,z6]),(0,[z21,z3,z4,z5,z6,z173])],[(0,[z0,z2,z3,z4,z946,z6])],[(0,[z32,z2,z3,z4,z403,z5]),(0,[z32,z126,z3,z4,z5,z6]),(0,[z0,z947,z3,z4,z5,z6]),(0,[z0,z948,z3,z4,z5,z6])],[(0,[z2,z3,z4,z43,z5,z6]),(0,[z0,z2,z3,z4,z361,z6])],[(0,[z109,z0,z2,z98,z5,z6]),(0,[z0,z2,z3,z949,z5,z6])],[(0,[z143,z2,z3,z4,z34,z6]),(0,[z0,z461,z4,z5,z10,z6]),(0,[z21,z0,z3,z4,z167,z5]),(0,[z2,z3,z120,z4,z43,z5]),(0,[z21,z0,z3,z4,z38,z22]),(0,[z23,z3,z4,z5,z10,z6])],[(0,[z79,z2,z3,z4,z5,z58]),(0,[z0,z2,z3,z950,z4,z5]),(0,[z21,z0,z2,z3,z4,z394])],[(0,[z32,z2,z220,z4,z5,z6]),(0,[z356,z3,z4,z5,z10,z6])],[],[(0,[z2,z3,z77,z4,z5,z6]),(0,[z21,z32,z3,z4,z5,z14]),(0,[z0,z2,z3,z187,z5,z9])],[(0,[z52,z3,z4,z5,z640,z6]),(0,[z32,z2,z3,z4,z5,z241]),(0,[z0,z2,z951,z4,z5,z6]),(0,[z456,z0,z3,z4,z54,z6]),(0,[z0,z2,z3,z398,z4,z5]),(0,[z0,z2,z3,z4,z5,z952])],[(0,[z953,z0,z3,z4,z5,z6]),(0,[z954,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z627]),(0,[z0,z37,z2,z3,z4,z394]),(0,[z955,z2,z3,z4,z5,z6]),(0,[z160,z0,z3,z4,z38,z22])]],
   [[(0,[z177,z2,z152,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z956]),(0,[z0,z235,z3,z4,z171,z6])],[(0,[z60,z2,z3,z4,z132,z6]),(0,[z0,z19,z3,z4,z5,z241]),(0,[z3,z4,z43,z5,z10,z6]),(0,[z0,z2,z3,z191,z766,z4])],[(0,[z21,z0,z3,z4,z103,z6]),(0,[z0,z235,z3,z4,z180,z6]),(0,[z0,z389,z3,z4,z5,z553]),(0,[z0,z3,z4,z5,z6,z957]),(0,[z0,z3,z958,z4,z5,z6]),(0,[z959,z2,z3,z4,z5,z6])],[(0,[z32,z2,z3,z4,z853,z6]),(0,[z2,z3,z960,z4,z5,z6])],[(0,[z0,z961,z3,z4,z5,z6]),(0,[z2,z81,z7,z4,z5,z6]),(0,[z0,z962,z3,z4,z5,z6]),(0,[z305,z3,z4,z5,z10,z6]),(0,[z21,z194,z3,z4,z5,z6]),(0,[z0,z3,z4,z103,z10,z6]),(0,[z0,z244,z3,z4,z5,z14])],[(0,[z21,z0,z3,z4,z5,z8]),(0,[z963,z2,z3,z4,z5,z6])],[(0,[z2,z353,z7,z4,z5,z6]),(0,[z0,z3,z4,z5,z964,z6]),(0,[z0,z2,z3,z66,z256,z5]),(0,[z2,z3,z965,z4,z5,z6])],[(0,[z21,z0,z3,z4,z5,z384]),(0,[z21,z0,z3,z4,z5,z611]),(0,[z21,z0,z3,z204,z4,z5]),(0,[z966,z3,z4,z5,z10,z6]),(0,[z0,z3,z967,z4,z5,z6]),(0,[z0,z2,z3,z36,z394,z89])],[(0,[z0,z2,z3,z159,z196,z6])],[(0,[z2,z7,z4,z512,z5,z6]),(0,[z3,z827,z4,z5,z10,z6]),(0,[z0,z3,z968,z4,z5,z6]),(0,[z0,z110,z3,z4,z394,z6])],[(0,[z0,z2,z152,z4,z5,z6]),(0,[z59,z2,z3,z444,z5,z6]),(0,[z969,z2,z3,z4,z5,z6])],[(0,[z0,z455,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z665,z6]),(0,[z21,z32,z3,z4,z5,z26])],[(0,[z2,z3,z7,z4,z403,z5]),(0,[z21,z50,z7,z4,z5,z6])],[(0,[z970,z2,z3,z4,z5,z6]),(0,[z21,z32,z3,z4,z5,z44]),(0,[z239,z32,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z971,z6]),(0,[z0,z37,z3,z230,z4,z5]),(0,[z0,z50,z130,z5,z10,z6]),(0,[z368,z389,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z972])],[(0,[z21,z0,z3,z4,z731,z6]),(0,[z973,z0,z3,z208,z4,z5])],[(0,[z149,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z221,z3,z4,z5,z265]),(0,[z0,z3,z4,z5,z548,z6]),(0,[z0,z126,z3,z4,z132,z6]),(0,[z169,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z53,z4,z5]),(0,[z0,z974,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z975]),(0,[z976,z0,z2,z4,z5,z6])],[(0,[z0,z977,z3,z4,z5,z6]),(0,[z60,z2,z3,z4,z880,z6]),(0,[z305,z2,z3,z4,z5,z241]),(0,[z0,z20,z4,z5,z6,z11]),(0,[z0,z3,z4,z5,z978,z6])],[(0,[z979,z2,z3,z4,z5,z6]),(0,[z0,z244,z3,z4,z5,z26])],[(0,[z240,z2,z3,z444,z5,z6]),(0,[z32,z2,z824,z4,z5,z6]),(0,[z21,z3,z372,z4,z5,z6]),(0,[z21,z0,z3,z66,z146,z5]),(0,[z2,z3,z4,z5,z6,z980]),(0,[z0,z2,z50,z791,z5,z6]),(0,[z194,z2,z3,z159,z5,z6]),(0,[z0,z2,z3,z917,z4,z5]),(0,[z981,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z982,z6]),(0,[z2,z3,z7,z4,z5,z241]),(0,[z32,z783,z3,z4,z5,z6]),(0,[z48,z21,z3,z4,z162,z6]),(0,[z428,z3,z4,z5,z10,z6]),(0,[z116,z3,z43,z209,z5,z6]),(0,[z0,z3,z115,z4,z5,z6]),(0,[z21,z0,z3,z36,z4,z441]),(0,[z0,z3,z983,z4,z5,z6]),(0,[z0,z2,z306,z4,z5,z26])],[(0,[z2,z3,z984,z4,z5,z6])],[(0,[z0,z3,z123,z4,z403,z5]),(0,[z0,z19,z75,z4,z5,z6]),(0,[z0,z37,z2,z3,z4,z103]),(1,[z0,z2,z4,z985,z6])],[(0,[z0,z2,z461,z4,z5,z58]),(0,[z0,z2,z3,z4,z5,z457]),(0,[z0,z3,z398,z4,z5,z54])],[(0,[z32,z2,z465,z4,z5,z6]),(0,[z116,z0,z3,z398,z209,z5]),(0,[z0,z3,z4,z5,z10,z349]),(0,[z0,z226,z4,z5,z150,z6])],[(0,[z32,z2,z3,z12,z15,z6]),(0,[z0,z110,z3,z4,z441,z6])],[(0,[z396,z3,z7,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z241]),(0,[z986,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z987,z6]),(0,[z988,z2,z3,z4,z5,z6])],[(0,[z52,z30,z3,z4,z5,z265]),(0,[z2,z3,z4,z989,z5,z6]),(0,[z868,z2,z7,z4,z5,z6]),(0,[z990,z2,z3,z4,z5,z6]),(0,[z991,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z163]),(0,[z0,z992,z3,z4,z5,z6]),(0,[z0,z2,z3,z121,z766,z4])],[(0,[z39,z2,z7,z4,z40,z6]),(0,[z32,z2,z3,z4,z5,z891]),(0,[z993,z2,z3,z4,z5,z6])],[(0,[z0,z3,z242,z4,z54,z6])],[(0,[z2,z7,z4,z5,z561,z6])]],
   [[(0,[z0,z3,z994,z4,z5,z6]),(0,[z147,z0,z3,z4,z5,z6]),(0,[z510,z0,z3,z4,z54,z6]),(0,[z0,z2,z3,z5,z6,z781])],[(0,[z0,z3,z4,z15,z548,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z169,z30,z3,z4,z5,z6]),(0,[z2,z3,z7,z155,z6,z76])],[(0,[z0,z2,z3,z995,z4,z6]),(0,[z32,z2,z217,z4,z196,z6]),(0,[z59,z2,z3,z17,z132,z6]),(0,[z2,z3,z4,z761,z5,z6]),(0,[z996,z0,z3,z4,z5,z6]),(0,[z422,z2,z3,z4,z5,z8]),(0,[z0,z997,z3,z4,z5,z6]),(0,[z998,z0,z3,z4,z5,z6])],[(0,[z194,z2,z3,z69,z5,z6]),(0,[z147,z23,z3,z4,z5,z6])],[(0,[z39,z21,z0,z4,z40,z6])],[(0,[z0,z2,z3,z4,z5,z999]),(0,[z133,z21,z3,z4,z5,z8]),(0,[z3,z372,z4,z5,z10,z6])],[(1,[z2,z3,z4,z880,z6]),(0,[z92,z0,z2,z791,z5,z6])],[(0,[z0,z2,z1000,z4,z5,z6])],[(0,[z32,z2,z697,z4,z5,z6]),(0,[z0,z2,z1001,z4,z5,z6])],[(0,[z32,z128,z3,z362,z5,z6]),(0,[z0,z2,z3,z4,z1002,z6])],[(0,[z63,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1003,z5,z6]),(0,[z496,z3,z4,z5,z10,z6])],[(0,[z32,z282,z3,z4,z5,z6]),(0,[z2,z3,z4,z1004,z5,z6])],[(0,[z0,z2,z3,z1005,z5,z6]),(0,[z0,z3,z1006,z4,z5,z6])],[(0,[z2,z7,z4,z592,z5,z6])],[(0,[z2,z3,z7,z12,z15,z6]),(0,[z21,z0,z3,z66,z4,z5]),(0,[z194,z113,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z734,z9])]],
   [[(0,[z30,z708,z3,z4,z5,z6]),(0,[z0,z3,z4,z209,z403,z5]),(0,[z21,z0,z3,z115,z4,z5])],[(0,[z21,z0,z3,z4,z5,z97]),(0,[z0,z2,z3,z4,z1007,z6]),(0,[z0,z2,z3,z4,z1008,z6]),(0,[z0,z2,z3,z15,z6,z781])],[(0,[z0,z2,z3,z4,z5,z1009]),(0,[z25,z3,z7,z4,z5,z6]),(0,[z0,z3,z4,z5,z1010,z6])],[(0,[z0,z1011,z3,z4,z5,z6]),(0,[z0,z1012,z3,z4,z5,z6]),(0,[z147,z0,z3,z4,z5,z80]),(0,[z0,z2,z3,z130,z180,z6]),(0,[z1013,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1014,z6]),(0,[z0,z3,z4,z5,z1015,z6]),(0,[z79,z3,z4,z5,z10,z80]),(0,[z21,z393,z3,z4,z5,z8]),(0,[z1016,z2,z3,z4,z5,z6]),(0,[z131,z0,z4,z5,z108,z14])],[(0,[z133,z25,z3,z4,z5,z8]),(0,[z1017,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z108]),(0,[z21,z0,z3,z36,z66,z5]),(0,[z0,z37,z3,z115,z4,z5])],[(0,[z0,z3,z4,z5,z6,z1018]),(0,[z116,z0,z3,z209,z336,z6]),(0,[z0,z3,z4,z403,z5,z10])],[(0,[z2,z491,z7,z4,z5,z6]),(0,[z1019,z2,z3,z4,z5,z6]),(0,[z3,z7,z4,z5,z6,z269]),(0,[z0,z2,z3,z4,z1020,z6]),(0,[z0,z3,z123,z398,z4,z5]),(0,[z0,z19,z20,z4,z5,z241]),(0,[z21,z3,z4,z43,z5,z6]),(0,[z0,z3,z191,z754,z4,z5]),(0,[z0,z1021,z3,z4,z5,z6]),(0,[z0,z1022,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1023]),(0,[z0,z226,z123,z4,z5,z6]),(0,[z0,z2,z3,z4,z1024,z6]),(0,[z0,z2,z3,z120,z4,z5])],[(0,[z953,z3,z7,z4,z5,z6]),(0,[z2,z7,z4,z616,z5,z6]),(0,[z3,z7,z4,z5,z1025,z6]),(0,[z116,z0,z3,z398,z4,z5])],[(0,[z32,z235,z3,z4,z5,z6]),(0,[z92,z0,z2,z98,z5,z6])],[(0,[z0,z2,z3,z1026,z4,z5]),(0,[z0,z2,z3,z4,z1027,z6]),(0,[z0,z2,z3,z4,z38,z124]),(0,[z2,z3,z4,z5,z6,z1028]),(0,[z0,z2,z3,z4,z5,z734])],[(0,[z0,z19,z3,z4,z403,z5])],[(0,[z422,z30,z3,z4,z5,z6]),(0,[z0,z2,z3,z1029,z5,z6]),(0,[z2,z3,z7,z4,z900,z6]),(0,[z0,z2,z3,z4,z5,z1030]),(0,[z0,z3,z69,z5,z10,z6]),(0,[z0,z1031,z3,z4,z5,z6])],[(0,[z0,z56,z3,z4,z796,z6]),(0,[z0,z3,z4,z5,z10,z811])],[(0,[z21,z3,z7,z4,z5,z8]),(0,[z32,z3,z4,z5,z927,z6]),(0,[z21,z0,z3,z4,z685,z5]),(0,[z0,z1032,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1033]),(0,[z357,z0,z3,z4,z5,z10]),(0,[z21,z0,z3,z4,z808,z6]),(0,[z0,z113,z3,z159,z5,z6]),(0,[z0,z3,z4,z5,z1034,z6])],[(0,[z0,z2,z3,z4,z1035,z6]),(0,[z2,z3,z7,z906,z5,z6]),(0,[z0,z2,z3,z1036,z4,z5]),(0,[z0,z56,z3,z4,z630,z6]),(0,[z0,z3,z4,z5,z10,z469]),(1,[z0,z2,z791,z5,z6])],[(0,[z30,z3,z4,z479,z5,z6]),(0,[z0,z2,z84,z4,z5,z915])],[(0,[z0,z126,z461,z4,z5,z6]),(0,[z0,z282,z3,z191,z121,z4])],[(0,[z0,z2,z3,z4,z171,z6])],[(0,[z32,z2,z84,z4,z5,z26]),(0,[z1037,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z36,z4,z5]),(0,[z369,z21,z0,z3,z4,z5]),(0,[z0,z3,z4,z5,z6,z1038]),(0,[z270,z3,z4,z5,z6,z388])],[(0,[z0,z2,z1039,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z591]),(0,[z0,z2,z3,z4,z180,z6])],[(0,[z2,z3,z7,z4,z5,z492]),(0,[z0,z3,z4,z5,z6,z1040]),(0,[z0,z3,z4,z5,z1041,z6]),(0,[z0,z1042,z3,z4,z5,z6]),(0,[z2,z3,z4,z1043,z5,z6]),(0,[z2,z3,z4,z5,z6,z1044])],[(0,[z368,z2,z3,z4,z5,z553])],[(0,[z2,z3,z7,z4,z5,z265]),(0,[z0,z886,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z668,z5]),(0,[z0,z2,z3,z4,z449,z6])],[(0,[z294,z3,z7,z4,z5,z6]),(0,[z0,z3,z4,z794,z5,z6]),(0,[z32,z244,z3,z4,z5,z6])],[(0,[z2,z3,z1045,z4,z5,z6]),(0,[z39,z0,z2,z4,z40,z469])],[(0,[z177,z3,z144,z5,z10,z6]),(0,[z21,z0,z3,z4,z5,z11]),(0,[z21,z368,z3,z4,z5,z6])],[(0,[z2,z50,z7,z98,z5,z6]),(0,[z140,z0,z2,z98,z5,z6]),(0,[z0,z3,z4,z548,z6,z76]),(0,[z319,z0,z3,z209,z5,z6]),(0,[z117,z0,z3,z4,z403,z54]),(0,[z21,z0,z50,z130,z5,z6]),(0,[z63,z2,z3,z4,z171,z6])],[(0,[z31,z221,z3,z4,z5,z6]),(0,[z704,z0,z3,z4,z5,z10]),(0,[z1046,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z103,z5]),(0,[z1047,z0,z3,z4,z5,z6])],[(0,[z32,z2,z3,z155,z6,z76]),(0,[z893,z2,z3,z4,z5,z6]),(0,[z63,z2,z3,z4,z180,z6]),(0,[z0,z2,z3,z4,z1048,z6])]],
   [[(0,[z21,z0,z3,z4,z5,z499]),(0,[z0,z1049,z3,z4,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z2,z50,z289,z130,z5,z6])],[(0,[z1051,z0,z3,z4,z5,z6]),(0,[z129,z0,z3,z146,z5,z6]),(0,[z0,z113,z3,z69,z5,z6]),(0,[z0,z2,z3,z36,z89,z441])],[(0,[z0,z3,z4,z132,z10,z6]),(0,[z21,z0,z3,z4,z5,z78]),(0,[z116,z0,z3,z120,z209,z5]),(0,[z21,z0,z3,z36,z4,z394])],[(0,[z0,z2,z3,z4,z5,z1052]),(0,[z32,z2,z3,z4,z361,z6]),(0,[z111,z2,z152,z4,z5,z6]),(0,[z148,z0,z763,z4,z5,z6])],[(0,[z0,z1053,z3,z4,z5,z6]),(0,[z21,z32,z7,z4,z5,z6]),(0,[z0,z1054,z3,z4,z5,z6]),(0,[z21,z0,z3,z638,z4,z5]),(0,[z0,z2,z3,z4,z5,z1055]),(0,[z0,z3,z155,z10,z6,z76])],[(0,[z2,z3,z4,z5,z6,z1056]),(0,[z2,z3,z4,z880,z102,z6]),(0,[z21,z0,z3,z4,z403,z5]),(0,[z0,z2,z3,z1057,z4,z5]),(0,[z1058,z2,z3,z4,z5,z6])],[(0,[z59,z2,z461,z17,z5,z6]),(0,[z21,z0,z3,z4,z5,z615]),(0,[z21,z0,z837,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1059,z6]),(0,[z0,z19,z653,z4,z5,z6])],[(0,[z21,z0,z3,z4,z5,z252])],[(0,[z0,z2,z3,z4,z1060,z6]),(0,[z21,z0,z841,z4,z5,z6]),(0,[z68,z0,z3,z4,z303,z6]),(0,[z2,z3,z1061,z4,z5,z6])],[(0,[z2,z3,z1062,z4,z5,z6]),(0,[z147,z3,z7,z4,z5,z6]),(0,[z32,z2,z3,z398,z4,z5]),(0,[z21,z0,z3,z4,z5,z150]),(0,[z39,z0,z4,z40,z10,z6])],[(0,[z30,z455,z3,z4,z5,z6]),(0,[z1063,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z361,z10,z6]),(0,[z0,z3,z230,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1064]),(0,[z21,z0,z3,z4,z103,z14])],[(0,[z0,z3,z4,z5,z796,z6]),(0,[z0,z3,z4,z5,z1065,z6]),(0,[z92,z0,z2,z98,z171,z6]),(0,[z0,z2,z3,z4,z1066,z6])],[(0,[z32,z56,z3,z4,z83,z6]),(0,[z0,z19,z3,z398,z4,z5])],[(0,[z389,z3,z7,z4,z5,z6]),(0,[z92,z0,z2,z98,z180,z6])],[(0,[z2,z7,z4,z5,z681,z6]),(0,[z0,z2,z3,z4,z1067,z6]),(0,[z59,z3,z17,z5,z10,z6]),(0,[z0,z3,z1068,z4,z5,z6]),(0,[z267,z2,z3,z4,z5,z80]),(0,[z0,z2,z3,z4,z1069,z6])]],
   [[(0,[z0,z126,z3,z4,z5,z58]),(0,[z1070,z0,z3,z4,z5,z492]),(0,[z1071,z2,z3,z4,z5,z6]),(0,[z0,z1072,z3,z4,z5,z6]),(0,[z973,z0,z3,z4,z5,z6])],[(0,[z60,z2,z3,z4,z102,z6]),(0,[z0,z2,z3,z766,z4,z38])],[(0,[z739,z2,z3,z4,z5,z6]),(0,[z530,z422,z3,z4,z5,z6]),(0,[z39,z356,z2,z4,z40,z6]),(0,[z0,z1073,z3,z4,z5,z6]),(0,[z0,z1074,z3,z4,z5,z6])],[(0,[z0,z2,z1075,z4,z5,z6]),(0,[z2,z3,z4,z901,z5,z6])],[(0,[z3,z7,z1076,z4,z5,z6]),(0,[z32,z2,z633,z4,z5,z6]),(0,[z177,z2,z3,z144,z5,z6]),(0,[z0,z3,z4,z5,z1077,z6])],[(0,[z0,z595,z3,z4,z5,z10]),(0,[z2,z7,z12,z98,z5,z6]),(0,[z0,z2,z3,z4,z1078,z6]),(0,[z0,z2,z3,z4,z985,z6])],[(0,[z39,z32,z2,z4,z40,z6]),(0,[z1079,z3,z4,z5,z10,z6])],[(0,[z52,z30,z3,z4,z5,z6]),(0,[z32,z455,z3,z4,z5,z6]),(0,[z0,z2,z3,z1080,z4,z6]),(0,[z39,z0,z396,z4,z40,z6])],[],[(0,[z21,z3,z7,z66,z4,z5]),(0,[z2,z3,z7,z4,z361,z6]),(0,[z0,z1081,z3,z4,z5,z6]),(0,[z0,z3,z268,z4,z5,z6]),(0,[z21,z0,z3,z191,z4,z5]),(0,[z0,z3,z4,z1082,z10,z6])],[(0,[z0,z152,z4,z5,z10,z6])],[(0,[z21,z0,z3,z155,z6,z76]),(0,[z239,z0,z3,z4,z103,z6])],[(0,[z32,z2,z3,z53,z4,z5]),(0,[z0,z2,z3,z4,z1083,z6]),(0,[z1084,z0,z3,z4,z5,z6]),(0,[z0,z84,z4,z5,z10,z26]),(0,[z0,z2,z3,z121,z4,z469])],[(0,[z29,z393,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z734,z6])],[(0,[z0,z2,z3,z4,z1085,z6]),(0,[z244,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z1086,z4,z6]),(0,[z1087,z0,z2,z4,z5,z6]),(0,[z21,z0,z341,z4,z5,z26]),(0,[z0,z3,z4,z5,z803,z553])],[(0,[z21,z0,z3,z4,z361,z6]),(0,[z0,z235,z3,z4,z5,z93]),(0,[z0,z3,z4,z5,z6,z1088]),(0,[z2,z3,z4,z5,z6,z1089]),(0,[z160,z0,z3,z191,z4,z5])]],
   [[(0,[z2,z3,z7,z398,z4,z5]),(0,[z131,z0,z2,z4,z5,z14]),(0,[z0,z2,z4,z5,z6,z1090])],[(0,[z21,z0,z3,z4,z5,z665]),(0,[z0,z2,z3,z4,z1091,z6])],[(0,[z188,z2,z3,z4,z5,z101]),(0,[z21,z0,z3,z4,z882,z6]),(0,[z2,z3,z4,z5,z6,z1092]),(0,[z2,z3,z4,z5,z6,z1093])],[(0,[z32,z2,z3,z4,z5,z457]),(0,[z0,z2,z50,z688,z5,z6]),(0,[z59,z2,z3,z17,z5,z58]),(0,[z0,z2,z3,z4,z1094,z6]),(0,[z0,z2,z3,z4,z1095,z6])],[(0,[z32,z2,z3,z4,z5,z492]),(0,[z0,z2,z3,z1096,z5,z6]),(0,[z0,z2,z4,z5,z6,z1097]),(0,[z0,z3,z4,z395,z403,z5])],[(0,[z0,z2,z3,z4,z1098,z5]),(0,[z300,z2,z3,z4,z5,z6]),(0,[z92,z2,z7,z98,z5,z6]),(0,[z32,z2,z598,z4,z5,z6]),(0,[z21,z177,z3,z144,z5,z6])],[(0,[z32,z2,z3,z4,z5,z265]),(0,[z0,z37,z3,z4,z5,z665]),(0,[z0,z2,z3,z1099,z5,z6]),(0,[z0,z2,z3,z4,z5,z99])],[(0,[z1081,z3,z7,z4,z5,z6]),(0,[z438,z2,z3,z4,z132,z6]),(0,[z21,z0,z3,z4,z509,z5])],[(0,[z0,z2,z3,z1100,z4,z5]),(0,[z117,z0,z3,z4,z54,z6]),(0,[z21,z0,z3,z12,z15,z6]),(0,[z0,z1101,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1102,z4,z5]),(0,[z169,z2,z3,z398,z4,z5]),(0,[z147,z0,z3,z4,z5,z14])],[(0,[z148,z428,z123,z4,z5,z6]),(0,[z0,z2,z3,z4,z1103,z5])],[(0,[z2,z3,z432,z144,z5,z6]),(0,[z21,z0,z3,z478,z4,z5]),(0,[z1104,z2,z3,z4,z5,z6])],[(0,[z0,z3,z120,z4,z5,z10])],[(0,[z1105,z0,z3,z4,z5,z6]),(0,[z92,z21,z0,z98,z5,z6]),(0,[z21,z137,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1106]),(0,[z1107,z2,z3,z4,z5,z6])],[(0,[z21,z3,z7,z36,z4,z5]),(0,[z2,z3,z4,z5,z6,z1108]),(0,[z0,z56,z3,z398,z4,z5]),(0,[z21,z0,z3,z331,z4,z5])]],
   [[(0,[z0,z1109,z3,z4,z5,z6]),(0,[z21,z3,z77,z4,z5,z6]),(0,[z1110,z2,z3,z4,z5,z6]),(0,[z1111,z2,z3,z4,z5,z6])],[(0,[z0,z1112,z3,z4,z5,z6]),(0,[z0,z455,z3,z4,z132,z6]),(0,[z0,z3,z4,z5,z1113,z6]),(0,[z0,z2,z3,z4,z1114,z5]),(0,[z21,z0,z3,z4,z5,z447]),(0,[z21,z1115,z3,z4,z5,z6]),(0,[z1116,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z10,z553]),(0,[z0,z2,z3,z159,z40,z6]),(0,[z0,z2,z3,z4,z5,z1117])],[(0,[z2,z3,z7,z53,z4,z5]),(0,[z32,z2,z3,z4,z5,z999]),(0,[z0,z2,z3,z1118,z4,z6]),(0,[z0,z2,z3,z1119,z5,z6]),(0,[z21,z0,z217,z4,z196,z6]),(0,[z21,z0,z3,z4,z5,z450]),(0,[z0,z2,z3,z36,z89,z5])],[(0,[z2,z250,z824,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z453]),(0,[z2,z3,z4,z1120,z5,z6])],[(0,[z2,z3,z314,z4,z5,z142]),(0,[z21,z32,z3,z4,z38,z5]),(0,[z0,z2,z3,z4,z1121,z6]),(0,[z21,z3,z4,z5,z8,z80]),(0,[z39,z0,z2,z4,z985,z6])],[(0,[z21,z0,z3,z4,z5,z118]),(0,[z0,z2,z1122,z4,z5,z6]),(0,[z194,z3,z4,z5,z10,z6]),(0,[z0,z3,z4,z441,z10,z6])],[(0,[z0,z2,z3,z1123,z5,z6]),(0,[z169,z455,z3,z4,z5,z6]),(0,[z21,z79,z3,z4,z5,z80]),(0,[z305,z2,z3,z4,z5,z457]),(0,[z1124,z2,z3,z4,z5,z6])],[(0,[z21,z0,z3,z4,z5,z274]),(0,[z2,z7,z4,z5,z141,z6]),(0,[z21,z0,z3,z4,z5,z275]),(0,[z0,z2,z3,z4,z1125,z6]),(0,[z21,z0,z3,z4,z440,z5]),(0,[z0,z1126,z3,z4,z5,z6]),(0,[z147,z0,z3,z4,z5,z26])],[(0,[z0,z2,z3,z4,z5,z1127]),(0,[z29,z562,z3,z4,z5,z6]),(0,[z356,z2,z3,z4,z5,z6]),(0,[z2,z1128,z3,z4,z5,z6]),(0,[z0,z3,z115,z4,z394,z6])],[(0,[z2,z3,z7,z4,z5,z457]),(0,[z3,z7,z4,z5,z6,z740]),(0,[z21,z32,z250,z4,z5,z6]),(0,[z133,z3,z4,z5,z8,z10]),(0,[z2,z3,z1129,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1130]),(0,[z32,z2,z3,z4,z935,z6]),(0,[z0,z2,z3,z4,z5,z1131]),(0,[z21,z0,z3,z4,z5,z290])],[(0,[z1115,z2,z3,z4,z5,z6])],[(0,[z368,z3,z4,z5,z10,z6]),(0,[z0,z3,z208,z4,z6,z76])],[(0,[z0,z1132,z3,z4,z5,z6]),(0,[z48,z2,z3,z4,z34,z6]),(0,[z21,z169,z3,z4,z5,z6]),(0,[z3,z4,z1133,z5,z10,z6]),(0,[z2,z217,z172,z4,z196,z6])],[(0,[z282,z3,z7,z4,z5,z6]),(0,[z32,z2,z334,z4,z5,z6]),(0,[z0,z2,z3,z4,z132,z492]),(0,[z0,z2,z3,z1134,z4,z6]),(0,[z1135,z2,z3,z4,z5,z6]),(0,[z131,z496,z2,z4,z5,z14]),(0,[z0,z2,z4,z5,z6,z915])],[(0,[z0,z2,z1136,z4,z5,z6]),(0,[z32,z1012,z3,z4,z5,z6]),(0,[z1137,z2,z3,z4,z5,z6]),(0,[z0,z3,z1138,z4,z5,z6])]],
   [[(0,[z32,z3,z4,z5,z1014,z6]),(0,[z21,z0,z3,z4,z5,z492]),(0,[z2,z3,z4,z1133,z5,z6]),(0,[z0,z2,z3,z791,z5,z6]),(0,[z0,z2,z3,z13,z4,z6])],[(0,[z305,z2,z3,z4,z5,z6]),(0,[z2,z7,z98,z5,z6,z76]),(0,[z0,z2,z3,z638,z89,z5])],[(0,[z21,z0,z3,z4,z5,z265]),(0,[z659,z0,z123,z4,z5,z6]),(0,[z0,z1139,z3,z4,z5,z6]),(0,[z0,z2,z3,z1140,z4,z5])],[(0,[z32,z2,z3,z4,z1020,z6]),(1,[z0,z2,z4,z5,z915])],[(0,[z2,z3,z7,z4,z5,z6]),(0,[z438,z2,z3,z4,z102,z6])],[(0,[z0,z2,z3,z4,z5,z1141]),(0,[z2,z3,z7,z995,z4,z6]),(0,[z0,z2,z3,z191,z121,z4])],[(0,[z1142,z2,z3,z4,z5,z6]),(0,[z21,z0,z75,z4,z5,z26]),(0,[z0,z2,z3,z4,z394,z6])],[(0,[z299,z393,z3,z4,z5,z6]),(0,[z1143,z0,z3,z4,z5,z6])],[(0,[z48,z3,z4,z162,z10,z6]),(0,[z0,z3,z115,z4,z441,z6])],[(0,[z0,z2,z3,z4,z5,z1144]),(0,[z0,z2,z3,z4,z5,z1145]),(0,[z0,z3,z4,z5,z6,z786])],[(0,[z21,z0,z3,z4,z5,z325])],[(0,[z0,z2,z3,z4,z5,z1146]),(0,[z0,z56,z3,z4,z5,z265]),(0,[z2,z7,z204,z4,z5,z6]),(0,[z1147,z2,z3,z4,z5,z6]),(0,[z21,z0,z217,z3,z4,z38]),(0,[z0,z3,z1148,z4,z5,z6]),(0,[z21,z0,z3,z571,z4,z5]),(0,[z0,z1149,z3,z4,z5,z6]),(0,[z131,z0,z2,z13,z4,z14])],[(0,[z0,z3,z1150,z4,z5,z6])],[(0,[z169,z2,z3,z4,z5,z6]),(0,[z30,z2,z152,z4,z5,z6]),(0,[z2,z694,z7,z4,z5,z6]),(0,[z0,z2,z3,z766,z4,z6])],[(0,[z0,z3,z4,z5,z10,z58]),(0,[z0,z2,z3,z4,z1151,z6]),(0,[z59,z21,z3,z17,z5,z6]),(0,[z1152,z2,z3,z4,z5,z6]),(0,[z1153,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1154,z6]),(0,[z375,z2,z3,z4,z5,z33]),(0,[z116,z32,z3,z209,z5,z6]),(0,[z820,z0,z3,z4,z5,z6]),(0,[z1155,z0,z3,z4,z5,z6]),(0,[z778,z3,z4,z5,z10,z6]),(0,[z0,z3,z13,z4,z10,z6])]],
   [[(0,[z52,z708,z3,z4,z5,z6]),(0,[z32,z2,z3,z4,z171,z6]),(0,[z21,z0,z3,z4,z5,z33]),(0,[z0,z2,z461,z4,z361,z6]),(0,[z21,z0,z3,z649,z4,z5]),(0,[z39,z0,z2,z159,z40,z6])],[(0,[z0,z2,z1156,z4,z5,z6])],[(0,[z32,z3,z4,z5,z6,z591]),(0,[z0,z2,z763,z4,z5,z6]),(0,[z2,z3,z1157,z4,z5,z6])],[(0,[z21,z3,z7,z191,z4,z5]),(0,[z767,z0,z3,z4,z5,z6]),(0,[z0,z1158,z3,z4,z5,z6]),(0,[z0,z128,z3,z271,z5,z6]),(0,[z0,z2,z4,z985,z40,z6]),(1,[z973,z0,z3,z4,z5])],[(0,[z19,z20,z7,z4,z5,z6]),(0,[z113,z3,z7,z4,z5,z6]),(0,[z140,z2,z3,z17,z5,z6]),(0,[z21,z0,z84,z4,z5,z26]),(0,[z782,z3,z4,z5,z10,z6]),(0,[z0,z3,z4,z103,z6,z108])],[(0,[z32,z2,z3,z4,z449,z6]),(0,[z21,z305,z3,z4,z5,z6]),(0,[z2,z3,z1159,z4,z5,z6])],[(0,[z0,z3,z4,z5,z10,z97]),(0,[z0,z2,z3,z4,z441,z6])],[(0,[z0,z2,z3,z4,z1160,z6]),(0,[z0,z1161,z3,z4,z5,z6]),(0,[z0,z3,z4,z171,z10,z6]),(0,[z104,z3,z4,z5,z10,z6]),(0,[z1162,z0,z3,z4,z5,z6])],[(0,[z887,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z880,z6]),(0,[z3,z77,z4,z5,z10,z6])],[(0,[z32,z2,z152,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1163]),(0,[z0,z2,z3,z4,z15,z403])],[(0,[z139,z2,z7,z4,z5,z6]),(0,[z32,z3,z4,z5,z665,z6])],[(0,[z131,z2,z7,z4,z5,z14]),(0,[z0,z2,z3,z1164,z4,z5]),(0,[z2,z3,z398,z4,z43,z5]),(0,[z21,z0,z3,z537,z4,z5]),(0,[z0,z3,z4,z5,z1165,z6]),(0,[z0,z2,z3,z621,z15,z6])],[(0,[z0,z3,z362,z802,z5,z6]),(0,[z0,z2,z3,z1166,z5,z6])],[(0,[z1,z3,z343,z4,z5,z6]),(0,[z2,z3,z7,z1026,z4,z5]),(0,[z1070,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z12,z6,z781])],[],[(0,[z2,z3,z144,z572,z5,z6]),(0,[z32,z3,z4,z5,z548,z6]),(0,[z0,z3,z170,z398,z4,z5]),(0,[z0,z2,z3,z4,z1167,z6]),(0,[z1168,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z432,z7,z98,z5,z6]),(0,[z0,z2,z3,z624,z6,z76]),(0,[z2,z3,z4,z1169,z5,z6]),(0,[z21,z0,z3,z4,z946,z6]),(0,[z0,z3,z4,z5,z1170,z6]),(0,[z0,z3,z1171,z4,z5,z6])],[(0,[z0,z1172,z3,z4,z5,z6]),(0,[z0,z2,z3,z425,z6,z76]),(0,[z39,z0,z2,z69,z40,z6])],[(0,[z117,z3,z7,z4,z54,z6]),(0,[z0,z2,z3,z4,z5,z1173]),(0,[z1174,z2,z3,z4,z5,z6]),(0,[z0,z1175,z3,z4,z5,z6])],[(0,[z402,z0,z3,z4,z5,z6]),(0,[z261,z2,z7,z4,z5,z6]),(0,[z32,z3,z115,z4,z5,z6]),(0,[z843,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z83,z6,z212]),(0,[z21,z0,z3,z4,z38,z124]),(0,[z131,z21,z0,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z93]),(0,[z0,z1176,z3,z4,z5,z6])],[(0,[z0,z455,z461,z4,z5,z6]),(1,[z2,z3,z761,z5,z6]),(0,[z0,z2,z3,z406,z15,z6])],[(0,[z21,z0,z3,z190,z4,z5]),(0,[z21,z0,z3,z251,z4,z5]),(0,[z0,z3,z4,z5,z811,z44])],[(0,[z2,z3,z7,z4,z171,z6]),(0,[z1011,z3,z7,z4,z5,z6]),(0,[z60,z2,z3,z4,z67,z6]),(0,[z21,z0,z3,z4,z5,z574]),(0,[z0,z1177,z3,z4,z5,z6])],[(0,[z32,z3,z230,z4,z5,z6]),(0,[z1178,z0,z3,z4,z5,z6]),(0,[z482,z2,z3,z4,z162,z6])],[(0,[z0,z495,z3,z4,z5,z6]),(0,[z496,z2,z3,z4,z5,z6]),(0,[z32,z250,z4,z5,z10,z6]),(0,[z2,z3,z155,z6,z88,z76])],[(0,[z21,z0,z3,z4,z5,z412]),(0,[z2,z127,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1179]),(0,[z872,z0,z3,z4,z5,z58]),(0,[z21,z0,z3,z398,z4,z5]),(0,[z0,z2,z3,z4,z5,z1180])],[(0,[z32,z2,z311,z4,z5,z6]),(0,[z0,z3,z4,z180,z10,z6])],[(0,[z2,z3,z7,z4,z449,z6])],[(0,[z0,z128,z3,z407,z5,z6]),(0,[z0,z3,z12,z15,z10,z6]),(0,[z63,z2,z3,z4,z5,z93])],[(0,[z318,z2,z3,z4,z42,z6]),(0,[z259,z2,z7,z4,z5,z6]),(0,[z1181,z2,z3,z4,z5,z6])],[(0,[z495,z3,z7,z4,z5,z6])],[(0,[z0,z3,z36,z115,z89,z5])]],
   [[(0,[z2,z3,z4,z5,z6,z1182])],[(0,[z32,z2,z3,z4,z5,z6]),(0,[z0,z2,z461,z4,z5,z492]),(0,[z79,z2,z3,z4,z5,z80]),(0,[z1183,z2,z3,z4,z5,z6]),(0,[z639,z0,z3,z4,z54,z6]),(0,[z21,z0,z3,z66,z256,z5])],[(0,[z2,z346,z7,z4,z5,z6]),(0,[z3,z7,z208,z4,z5,z6]),(0,[z0,z2,z3,z434,z6,z76])],[(0,[z0,z2,z152,z4,z132,z6]),(0,[z0,z2,z3,z4,z336,z6]),(0,[z117,z0,z3,z53,z4,z54]),(0,[z0,z3,z53,z4,z5,z10]),(0,[z0,z3,z4,z5,z1184,z6]),(0,[z2,z3,z4,z5,z6,z1185])],[(0,[z0,z2,z3,z4,z1186,z6]),(0,[z39,z0,z2,z4,z567,z6])],[(0,[z21,z0,z152,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z296])],[(0,[z3,z7,z4,z5,z10,z6]),(0,[z1187,z2,z3,z4,z5,z6]),(0,[z368,z2,z4,z98,z5,z6]),(0,[z39,z194,z2,z4,z40,z6])],[(0,[z318,z2,z3,z4,z102,z6]),(0,[z0,z2,z3,z98,z180,z6]),(0,[z1188,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1189,z4,z5]),(0,[z32,z2,z3,z4,z1083,z6]),(0,[z0,z3,z4,z5,z6,z1190])],[(0,[z23,z2,z3,z4,z5,z6]),(0,[z0,z1191,z3,z4,z5,z6]),(1,[z0,z763,z4,z5,z6]),(0,[z0,z590,z3,z4,z83,z6])],[(0,[z0,z2,z3,z4,z1192,z6]),(0,[z21,z0,z3,z520,z4,z5]),(0,[z0,z235,z3,z4,z5,z553]),(0,[z0,z1193,z3,z4,z5,z6])],[(0,[z140,z2,z7,z98,z5,z6]),(0,[z2,z3,z7,z4,z1060,z6]),(0,[z0,z495,z3,z4,z5,z80]),(0,[z21,z0,z3,z53,z4,z5]),(0,[z92,z0,z2,z98,z5,z93])],[(0,[z0,z2,z3,z4,z5,z1194]),(0,[z21,z32,z3,z4,z5,z8]),(0,[z0,z3,z1195,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1196,z6]),(0,[z2,z3,z372,z4,z5,z241]),(0,[z215,z0,z3,z4,z124,z6])],[(0,[z0,z3,z4,z5,z6,z1197]),(0,[z0,z3,z4,z1198,z5,z548]),(0,[z835,z21,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z469]),(0,[z2,z3,z1199,z4,z5,z6])],[(0,[z0,z774,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z409,z5]),(0,[z21,z0,z3,z448,z4,z5]),(0,[z1200,z0,z3,z4,z5,z6])]],
   [[(0,[z32,z2,z260,z4,z5,z6]),(0,[z0,z2,z3,z1201,z5,z6]),(0,[z0,z2,z3,z200,z5,z9]),(0,[z0,z2,z3,z4,z718,z6]),(0,[z0,z56,z3,z4,z303,z6])],[(0,[z1202,z2,z3,z4,z5,z6]),(0,[z0,z3,z207,z4,z5,z10]),(0,[z1203,z2,z3,z4,z5,z6]),(0,[z1204,z2,z3,z4,z5,z6])],[(0,[z21,z0,z3,z4,z5,z504]),(0,[z32,z2,z3,z4,z5,z99]),(0,[z21,z0,z3,z4,z5,z457]),(0,[z0,z3,z4,z5,z10,z241]),(0,[z0,z2,z4,z5,z985,z6])],[(0,[z117,z0,z3,z4,z124,z6]),(0,[z0,z2,z3,z4,z1205,z6])],[(0,[z32,z3,z4,z5,z6,z108]),(0,[z0,z3,z763,z4,z5,z6])],[(0,[z368,z235,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z171,z93])],[(0,[z169,z221,z3,z4,z5,z6]),(0,[z2,z824,z7,z4,z5,z6]),(0,[z0,z1206,z3,z4,z5,z6])],[(0,[z32,z2,z3,z120,z4,z5]),(0,[z2,z3,z4,z5,z880,z6]),(0,[z966,z2,z3,z4,z5,z6]),(0,[z62,z0,z341,z4,z5,z6]),(0,[z0,z2,z3,z36,z91,z5]),(0,[z0,z2,z3,z4,z180,z93]),(0,[z131,z0,z2,z4,z5,z915])],[(0,[z1207,z2,z3,z4,z5,z6])],[(0,[z79,z2,z152,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1198,z5]),(0,[z1208,z0,z3,z4,z5,z6])],[(0,[z0,z294,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z132,z6]),(0,[z0,z396,z3,z4,z5,z6]),(0,[z0,z1209,z3,z4,z5,z6])],[(1,[z2,z3,z4,z5,z749]),(0,[z23,z2,z3,z4,z5,z80]),(0,[z356,z2,z3,z4,z5,z99])],[(0,[z21,z0,z3,z4,z5,z6]),(0,[z32,z1112,z3,z4,z5,z6]),(0,[z0,z1210,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1211]),(0,[z21,z0,z3,z184,z4,z5]),(0,[z92,z0,z389,z98,z5,z6])],[(0,[z32,z2,z3,z36,z89,z5])],[(0,[z452,z0,z3,z209,z5,z6]),(0,[z1212,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z209,z449,z6]),(0,[z0,z3,z4,z698,z54,z6]),(0,[z281,z3,z4,z5,z10,z6]),(0,[z368,z2,z50,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z781])]],
   [[(0,[z2,z3,z7,z4,z1085,z6]),(0,[z48,z2,z3,z4,z162,z6]),(0,[z0,z3,z4,z802,z5,z6]),(0,[z0,z3,z4,z5,z786,z14]),(0,[z1213,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1214,z4,z5]),(0,[z21,z23,z3,z4,z5,z6]),(0,[z3,z4,z5,z10,z6,z88]),(0,[z92,z63,z2,z98,z5,z6])],[(0,[z59,z126,z3,z17,z5,z6]),(0,[z21,z0,z3,z4,z5,z525]),(0,[z0,z2,z3,z4,z5,z915])],[(0,[z31,z3,z185,z4,z5,z6]),(0,[z0,z2,z3,z4,z1215,z6]),(0,[z160,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z196,z985,z6]),(0,[z0,z2,z3,z332,z6,z76])],[(0,[z428,z2,z3,z4,z5,z6]),(0,[z148,z32,z123,z4,z5,z6]),(0,[z1216,z2,z3,z4,z5,z6])],[(0,[z32,z2,z3,z4,z180,z6]),(0,[z0,z2,z3,z4,z1082,z6])],[(0,[z0,z2,z3,z846,z5,z6])],[(0,[z147,z32,z3,z4,z5,z6]),(0,[z0,z2,z3,z858,z4,z5]),(0,[z116,z0,z3,z256,z5,z6]),(0,[z0,z3,z242,z186,z4,z6])],[(0,[z139,z7,z4,z5,z10,z6]),(0,[z2,z3,z7,z4,z5,z99]),(0,[z0,z3,z4,z5,z923,z58]),(0,[z21,z0,z3,z4,z5,z542]),(0,[z0,z293,z3,z155,z6,z76]),(0,[z2,z3,z1217,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1218,z6]),(0,[z32,z1132,z3,z4,z5,z6]),(0,[z0,z3,z1219,z4,z5,z6]),(0,[z0,z2,z3,z766,z4,z5])],[(0,[z0,z1220,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1221,z492]),(0,[z2,z3,z4,z5,z8,z508]),(0,[z0,z1222,z3,z4,z5,z6]),(0,[z0,z2,z660,z130,z5,z6])],[],[(0,[z32,z2,z3,z13,z4,z6]),(0,[z0,z3,z4,z5,z6,z811]),(0,[z0,z396,z3,z4,z5,z99]),(0,[z0,z3,z4,z5,z1034,z469])],[(0,[z1223,z0,z3,z4,z5,z6]),(0,[z2,z3,z7,z120,z4,z5]),(0,[z402,z3,z7,z4,z5,z6]),(0,[z79,z3,z4,z5,z665,z80]),(0,[z21,z0,z3,z165,z4,z5]),(0,[z0,z2,z3,z1224,z5,z6])],[(0,[z0,z1225,z3,z4,z5,z6]),(0,[z21,z0,z3,z1099,z5,z6]),(0,[z438,z3,z4,z5,z10,z6])],[(0,[z59,z2,z3,z367,z5,z6]),(0,[z0,z19,z20,z4,z5,z457]),(0,[z21,z0,z3,z4,z5,z559])]],
   [[(0,[z21,z0,z3,z4,z5,z80]),(0,[z21,z0,z3,z4,z646,z5]),(0,[z0,z3,z66,z5,z10,z9]),(0,[z245,z0,z2,z4,z5,z14])],[(0,[z2,z7,z443,z4,z5,z6]),(0,[z32,z2,z3,z191,z121,z4]),(0,[z2,z3,z1226,z4,z5,z6]),(0,[z0,z3,z1227,z4,z5,z6])],[(0,[z32,z2,z3,z4,z394,z6]),(0,[z438,z21,z3,z4,z5,z6])],[(0,[z0,z1228,z3,z4,z5,z6]),(0,[z0,z3,z1229,z4,z5,z6]),(0,[z21,z0,z3,z120,z4,z5]),(0,[z1079,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1230]),(0,[z0,z128,z3,z146,z5,z6])],[(0,[z2,z3,z7,z36,z89,z5]),(0,[z0,z2,z3,z89,z5,z734])],[(0,[z0,z389,z3,z4,z171,z6])],[(0,[z0,z3,z4,z5,z54,z265]),(0,[z21,z32,z3,z66,z4,z5]),(0,[z0,z1231,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1232,z6]),(0,[z169,z2,z3,z120,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1233]),(0,[z0,z2,z3,z1234,z4,z5]),(0,[z92,z0,z98,z5,z10,z6])],[(0,[z56,z3,z7,z4,z83,z6]),(0,[z0,z2,z401,z4,z5,z26])],[(0,[z1235,z0,z3,z4,z5,z6]),(0,[z0,z1236,z3,z4,z5,z6])],[(0,[z0,z19,z20,z4,z5,z6])],[(0,[z2,z3,z7,z4,z180,z6]),(0,[z0,z2,z3,z4,z5,z738]),(0,[z21,z0,z3,z4,z5,z702]),(0,[z2,z3,z1237,z4,z5,z6]),(0,[z21,z496,z3,z4,z5,z6]),(0,[z1238,z2,z3,z4,z5,z6]),(0,[z104,z2,z84,z4,z5,z26])],[(0,[z898,z21,z3,z4,z5,z6]),(0,[z0,z2,z130,z791,z5,z6])],[(0,[z0,z2,z3,z4,z777,z6]),(0,[z148,z0,z341,z4,z5,z6]),(0,[z0,z3,z4,z38,z10,z22]),(0,[z0,z2,z3,z121,z159,z6])],[(0,[z21,z3,z7,z4,z5,z142]),(0,[z0,z2,z3,z4,z5,z779]),(0,[z0,z3,z4,z5,z1170,z93]),(0,[z131,z281,z2,z4,z5,z14]),(0,[z973,z0,z3,z155,z4,z5])],[(0,[z59,z21,z3,z4,z5,z8]),(0,[z21,z0,z3,z4,z171,z6])]],
   [[(0,[z2,z3,z4,z5,z6,z1239]),(0,[z0,z2,z3,z4,z361,z58]),(0,[z0,z2,z3,z4,z5,z1240]),(0,[z1241,z2,z3,z4,z5,z6]),(0,[z104,z244,z3,z4,z5,z6])],[(0,[z92,z32,z2,z98,z5,z6]),(1,[z0,z3,z4,z1198,z5]),(0,[z0,z19,z763,z4,z5,z6]),(0,[z21,z0,z3,z4,z180,z6]),(0,[z21,z0,z3,z187,z4,z5]),(0,[z137,z3,z4,z5,z10,z6]),(0,[z0,z1242,z3,z4,z5,z6])],[(0,[z2,z3,z7,z13,z4,z6]),(0,[z32,z2,z3,z4,z441,z6]),(0,[z21,z0,z3,z85,z4,z5])],[(0,[z1243,z3,z7,z4,z5,z6]),(0,[z32,z2,z3,z4,z1160,z6]),(0,[z21,z0,z3,z61,z4,z5]),(0,[z0,z2,z3,z4,z5,z1244]),(0,[z0,z3,z4,z5,z6,z1245]),(0,[z2,z3,z1246,z4,z5,z6])],[(0,[z0,z3,z1247,z4,z5,z6]),(0,[z21,z0,z3,z4,z449,z6]),(0,[z1248,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z787,z6]),(0,[z133,z2,z3,z4,z5,z749]),(0,[z0,z1249,z3,z4,z5,z6])],[(0,[z2,z7,z507,z4,z5,z6]),(0,[z2,z152,z4,z5,z8,z6]),(0,[z1250,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z269]),(0,[z0,z128,z3,z802,z5,z6])],[(0,[z2,z3,z7,z191,z121,z4]),(0,[z21,z0,z3,z4,z5,z142]),(0,[z0,z2,z4,z5,z26,z915])],[(0,[z2,z3,z7,z4,z394,z6]),(0,[z0,z3,z4,z5,z1025,z6]),(0,[z32,z3,z268,z4,z5,z6]),(0,[z0,z2,z1251,z4,z5,z6]),(0,[z21,z0,z3,z13,z4,z6]),(0,[z0,z1252,z3,z4,z5,z6]),(0,[z0,z1253,z3,z4,z5,z6])],[(0,[z0,z3,z4,z1254,z5,z6])],[(0,[z21,z0,z3,z4,z5,z154]),(0,[z0,z2,z3,z4,z403,z76]),(0,[z1255,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1256,z6]),(0,[z1257,z0,z3,z4,z5,z6])],[(0,[z2,z7,z4,z98,z5,z6]),(0,[z1243,z0,z3,z4,z5,z6]),(0,[z21,z32,z3,z36,z4,z5]),(0,[z21,z0,z3,z415,z4,z5]),(0,[z21,z0,z3,z4,z546,z5]),(0,[z249,z3,z4,z5,z504,z6])],[(0,[z0,z2,z3,z4,z1258,z6]),(0,[z2,z3,z1259,z4,z5,z6]),(0,[z0,z765,z3,z4,z5,z6]),(0,[z0,z1260,z3,z4,z5,z6]),(0,[z1261,z2,z3,z4,z5,z6])],[(0,[z0,z2,z461,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z811]),(0,[z0,z2,z3,z4,z5,z553])],[(0,[z32,z2,z3,z4,z5,z93]),(0,[z2,z3,z4,z162,z880,z6]),(0,[z1262,z2,z3,z4,z5,z6]),(0,[z0,z1263,z3,z4,z5,z6])]],
   [[(0,[z297,z2,z7,z4,z5,z6]),(0,[z1264,z0,z3,z4,z5,z6])],[(0,[z1265,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z913,z6])],[(0,[z194,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z806]),(0,[z0,z2,z3,z4,z1266,z6]),(0,[z21,z0,z3,z476,z4,z5]),(0,[z21,z0,z3,z4,z5,z108]),(0,[z0,z2,z3,z4,z5,z1267])],[(0,[z0,z2,z152,z4,z5,z58])],[(0,[z21,z0,z3,z4,z5,z101]),(0,[z0,z455,z3,z4,z5,z58]),(0,[z3,z289,z4,z5,z10,z6])],[],[(0,[z0,z389,z3,z4,z5,z6]),(0,[z21,z104,z3,z4,z5,z6]),(0,[z1268,z2,z3,z4,z5,z6])],[(0,[z21,z3,z7,z4,z5,z6]),(0,[z0,z2,z3,z1269,z5,z6]),(0,[z0,z2,z3,z4,z5,z1270]),(0,[z63,z2,z3,z4,z5,z553]),(0,[z2,z84,z77,z4,z5,z26])],[(0,[z2,z3,z7,z4,z441,z6]),(0,[z760,z0,z3,z4,z5,z6]),(0,[z109,z0,z2,z4,z40,z6]),(0,[z0,z2,z3,z577,z6,z76]),(0,[z1271,z2,z3,z4,z5,z6])],[(0,[z368,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1272,z6]),(0,[z0,z2,z3,z4,z1273,z6]),(0,[z0,z3,z4,z796,z54,z6]),(0,[z0,z3,z36,z1138,z4,z5])],[(0,[z0,z3,z4,z403,z83,z5])],[(0,[z2,z408,z7,z4,z5,z6]),(0,[z111,z2,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1274])],[(0,[z2,z416,z7,z4,z5,z6]),(0,[z148,z149,z123,z4,z5,z6]),(0,[z0,z2,z791,z98,z5,z6])],[(0,[z2,z3,z7,z1164,z4,z5]),(0,[z160,z3,z7,z4,z5,z6]),(0,[z59,z2,z3,z17,z5,z492]),(0,[z21,z0,z3,z4,z5,z10]),(0,[z21,z0,z3,z236,z4,z5])],[(0,[z420,z2,z7,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1275]),(0,[z0,z128,z3,z4,z403,z5]),(0,[z1276,z2,z3,z4,z5,z6])],[(0,[z32,z2,z485,z4,z5,z6]),(0,[z32,z2,z3,z4,z336,z6]),(0,[z1277,z2,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z647,z5]),(0,[z63,z389,z3,z4,z5,z6]),(0,[z0,z2,z105,z4,z196,z6])]],
   [[(0,[z293,z3,z7,z4,z5,z6]),(0,[z32,z2,z3,z4,z1186,z6])],[(0,[z0,z3,z398,z362,z4,z5])],[(0,[z148,z7,z123,z4,z5,z6]),(0,[z0,z3,z1278,z4,z5,z6])],[(0,[z2,z3,z7,z1086,z4,z6]),(0,[z0,z2,z3,z4,z5,z1279]),(0,[z1280,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z159,z5,z6])],[(0,[z100,z2,z3,z4,z5,z8]),(1,[z0,z2,z3,z5,z734])],[(0,[z2,z3,z7,z4,z5,z93]),(0,[z2,z605,z7,z4,z5,z6]),(0,[z300,z2,z7,z4,z5,z6]),(0,[z2,z3,z1281,z4,z5,z6]),(0,[z0,z2,z217,z4,z985,z6]),(0,[z0,z2,z3,z766,z4,z22])],[(0,[z0,z1282,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1283,z6]),(0,[z92,z0,z2,z98,z5,z553])],[(0,[z2,z7,z4,z5,z6,z574]),(0,[z2,z3,z144,z761,z5,z6]),(0,[z39,z0,z113,z4,z40,z6])],[(0,[z32,z2,z3,z4,z5,z1194]),(0,[z79,z2,z3,z4,z5,z101])],[(0,[z1284,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z6,z781,z76]),(0,[z147,z0,z3,z66,z5,z9])],[(0,[z21,z3,z7,z4,z5,z80]),(0,[z21,z1116,z3,z4,z5,z6]),(0,[z131,z239,z0,z4,z5,z14])],[(0,[z0,z2,z3,z4,z5,z58]),(0,[z177,z2,z3,z761,z5,z6])],[(0,[z0,z2,z3,z840,z4,z6]),(0,[z0,z126,z3,z4,z361,z6]),(0,[z0,z3,z4,z5,z1272,z80]),(0,[z0,z3,z4,z458,z5,z10]),(0,[z21,z0,z3,z4,z1091,z6]),(0,[z0,z3,z251,z480,z5,z6])],[(0,[z0,z1285,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1286,z6]),(0,[z21,z0,z3,z4,z38,z76]),(0,[z973,z0,z2,z3,z4,z5])],[(0,[z32,z2,z7,z4,z5,z6]),(0,[z0,z3,z398,z4,z5,z10])],[(0,[z0,z1287,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z1288,z4,z5,z6]),(0,[z21,z32,z3,z191,z4,z5]),(0,[z2,z3,z4,z5,z6,z88]),(0,[z21,z0,z3,z4,z5,z1272]),(0,[z0,z2,z3,z4,z171,z553])],[(0,[z21,z0,z3,z4,z5,z99])],[(0,[z868,z2,z50,z4,z5,z6]),(0,[z32,z1206,z3,z4,z5,z6]),(0,[z2,z152,z4,z17,z5,z6]),(0,[z0,z2,z1289,z4,z5,z6]),(0,[z0,z2,z3,z4,z180,z553])],[(0,[z0,z3,z1076,z4,z5,z6]),(0,[z0,z20,z763,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z657]),(0,[z137,z2,z217,z4,z196,z6])],[(0,[z3,z7,z4,z5,z6,z591]),(0,[z0,z1290,z3,z4,z5,z6]),(0,[z2,z3,z4,z884,z5,z6]),(0,[z0,z2,z3,z69,z5,z6]),(0,[z0,z2,z3,z1291,z4,z6]),(0,[z356,z2,z3,z4,z5,z469]),(0,[z1292,z2,z3,z4,z5,z6])],[(0,[z2,z3,z7,z4,z336,z6]),(0,[z0,z2,z3,z761,z5,z6]),(0,[z133,z2,z3,z4,z5,z8]),(1,[z0,z3,z4,z5,z811])],[(0,[z0,z2,z3,z1293,z4,z5]),(0,[z0,z2,z3,z4,z5,z1294]),(1,[z2,z824,z4,z5,z6]),(0,[z1295,z0,z3,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z14]),(0,[z21,z0,z3,z4,z38,z303]),(0,[z2,z3,z4,z5,z6,z1296])],[(0,[z708,z221,z3,z4,z5,z6]),(0,[z32,z396,z3,z4,z5,z6]),(0,[z131,z32,z2,z4,z5,z14]),(0,[z32,z2,z3,z4,z132,z6]),(0,[z0,z3,z4,z5,z1221,z6]),(0,[z0,z1297,z3,z4,z5,z6]),(0,[z1298,z2,z3,z4,z5,z6]),(0,[z147,z3,z4,z5,z6,z173])],[(0,[z37,z3,z7,z4,z5,z10]),(0,[z0,z3,z4,z1198,z162,z5]),(0,[z0,z3,z1299,z4,z5,z6]),(0,[z0,z2,z3,z415,z121,z4])],[(0,[z21,z0,z3,z515,z4,z5])],[(0,[z0,z2,z3,z4,z5,z861]),(0,[z2,z3,z4,z5,z8,z58]),(0,[z0,z389,z3,z4,z180,z6]),(0,[z1284,z0,z3,z4,z5,z99]),(0,[z0,z3,z4,z5,z6,z1300])],[(0,[z2,z461,z7,z4,z5,z6]),(0,[z21,z0,z3,z4,z5,z695]),(0,[z368,z2,z3,z4,z171,z6]),(0,[z0,z1301,z3,z4,z5,z6])],[(0,[z1302,z2,z3,z4,z5,z6]),(0,[z3,z7,z4,z5,z665,z6]),(0,[z0,z3,z4,z1198,z5,z6]),(0,[z1303,z2,z3,z4,z5,z6]),(0,[z164,z0,z4,z5,z6,z11]),(0,[z0,z3,z4,z5,z6,z1304]),(0,[z160,z0,z3,z4,z5,z14]),(0,[z0,z1305,z3,z4,z5,z6])],[(0,[z0,z3,z1306,z4,z5,z6]),(0,[z21,z0,z3,z36,z89,z5])],[(0,[z0,z2,z1307,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1308]),(0,[z0,z2,z3,z4,z38,z22])],[(0,[z0,z2,z1309,z4,z5,z6]),(0,[z117,z32,z3,z4,z54,z6]),(0,[z0,z126,z152,z4,z5,z6]),(0,[z59,z2,z3,z17,z361,z6]),(0,[z0,z113,z3,z4,z5,z6]),(0,[z21,z0,z3,z1138,z4,z5]),(0,[z0,z2,z217,z543,z4,z6]),(0,[z0,z3,z13,z4,z6,z108])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 498) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 498).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 995).take 425) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1420)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [498, 497, 425] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 139).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 139).take 144).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 283).take 140).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 423).take 89).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [139, 144, 140, 89] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_38753

theorem PEqualNP.Outside.L_meta_38753 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4006144200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38753.solve