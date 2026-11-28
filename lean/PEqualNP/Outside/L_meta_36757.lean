import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36757

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
  Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x60c20294120a4149#64 ++ 0xcd021658903162d2#64 ++ 0xe3c60ffc7e3fc7fb#64 ++ 0xffd33f789a39f3f3#64 : BitVec 256),
   (0xa548502884448891#64 ++ 0xcd089816c18458b8#64 ++ 0xfff9f07f8fc7f8ff#64 ++ 0xdfacd89fe5c67cfc#64 : BitVec 256),
   (0x0214a50008911222#64 ++ 0x103060a02e028505#64 ++ 0x03ffff800ff9ff3e#64 ++ 0xf570e0e0fe078f1f#64 : BitVec 256),
   (0xc80139cd2001e402#64 ++ 0x10b700ed07680f60#64 ++ 0xfc01fffff001ffc3#64 ++ 0x59bf00ff07f80fe0#64 : BitVec 256),
   (0x0001ce724f200002#64 ++ 0x123ded0006dfb000#64 ++ 0x0001fffffffe0003#64 ++ 0x9e3fff0007fff000#64 : BitVec 256),
   (0x13a0000000000003#64 ++ 0xe03ffbfbf8000000#64 ++ 0xfffe000000000003#64 ++ 0xe03ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [13, 7]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z1 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x03ffffffffffff3f 0xff7fffe0ffffff1f

def z2 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000003 0xe03ffffff8000000

def z3 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c60ffc7e3fc7fb 0xffd33f789a39f3f3

def z4 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f07f8fc7f8ff 0xdfacd89fe5c67cfc

def z5 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z6 : W := mkw 0xed4979eda445ec93 0xddbf98ffc7ec5ff8 0xfff9ffffffc7ffff 0xdfbfd8ffe7fe7ffc

def z7 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffffffe0003 0x9e3fff0007fff000

def z8 : W := mkw 0x62d7eff65fbb536b 0xdf3ffff8befff7d7 0xe3ffffffffffffff 0xfffffff8ffffffff

def z9 : W := mkw 0x0080021002000001 0xc002165890112000 0xe3c60ffc7e3e0003 0xfe133f789a39f000

def z10 : W := mkw 0x0200000000000002 0x003060a028000000 0x03fe000000000002 0xe030e0e0f8000000

def z11 : W := mkw 0xc80139cd2001e400 0x1087004d07680f60 0xfc01fffff001ffc1 0x198f001f07f80fe0

def z12 : W := mkw 0x8508502884448890 0x0008880641841828 0x1c00000380000000 0x000c000701c00000

def z13 : W := mkw 0x0000402004000000 0x0008880000841000 0x03f9f07f8fc7f83f 0xdf2cd880e5c67c1c

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x03f9f0000fc1f83e 0xd520c080e4060c1c

def z15 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0000007ff0060001 0x0a0f1f0001f87000

def z16 : W := mkw 0x60420294120a4148 0x0d000400003162d2 0x00000ffc7e3fc7f8 0x1fc000000239f3f3

def z17 : W := mkw 0x0000000000000002 0x003de90000000000 0x0000000000000003 0x803fff0000000000

def z18 : W := mkw 0x13a0000000000001 0xe00212fbf8000000 0xfffe000000000000 0x600000fff8000000

def z19 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f00381c1f8fc 0x41acc09fe5c60cfc

def z20 : W := mkw 0x0080000000000003 0xc03ffb5890000000 0xe3c6000000000003 0xe03fff7898000000

def z21 : W := mkw 0x12a0000000000002 0x203febe938000000 0x0006000000000003 0xa03fff6018000000

def z22 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfc00000000000001 0x000f1f1f00000000

def z23 : W := mkw 0x13a0000000000001 0xe008fb12f8000000 0x03fe000000000000 0xa000ff00f8000000

def z24 : W := mkw 0x8508502884448890 0x0008880641841828 0x1c39f00381c03804 0x002cc08765c60c0c

def z25 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfffffffffff9ffff 0xfdffe0ffffff8fff

def z26 : W := mkw 0xf7ea52bc964ec9db 0xed3ffffff9b57afa 0xffffffffffffffff 0xffffffffffffffff

def z27 : W := mkw 0x20c20210120a0149 0xcd00161090116092 0x03c600000e3e0038 0xa6403f009801f013

def z28 : W := mkw 0x880139492001a402 0x10b500a507480d20 0x1c01f00380003800 0x002c008705c00c00

def z29 : W := mkw 0x13a0840008000003 0xf03ffbfbfe028000 0xffffff800ff80003 0xf43ffffffe078000

def z30 : W := mkw 0xa548100880448891 0xcd001016c10048b8 0xfc000000000000c0 0x0080001f000000e0

def z31 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe0000ffc7e3e00c3 0x9e933f180239f0e0

def z32 : W := mkw 0x2548c632cf640891 0xcf08fd12c097f098 0x03f800000ffe003c 0x8600ff00e007f01c

def z33 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xffffff800ff9ff3f 0xf57ffffffe078f1f

def z34 : W := mkw 0xdbb5bdcd2891f623 0xf0bffbffff6a8f65 0xfffffffffff9ffff 0xfdffffffffff8fff

def z35 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc07fffff039ffc3 0x79ff20ff1ff98fe3

def z36 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc00007ff00000c1 0x088f001f01f800e0

def z37 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0x1ff9f0038fc6383c 0x862cd887e5c67c1c

def z38 : W := mkw 0xc800108d2000e400 0x0082004d01200a60 0xfc000000000000c0 0x0080001f000000e0

def z39 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xffc6000000000003 0xe01f3f7f98000000

def z40 : W := mkw 0x12b4a50008911222 0x303763e93e028505 0x00060f8000380700 0x205327601a018303

def z41 : W := mkw 0x61c20294120a4149 0xcd0a9e5ad03162d2 0xfffe0ffc7e3fc7fb 0xfffffffffa39f3f3

def z42 : W := mkw 0x72e20294120a414b 0xed3777f9b83162d2 0xe3c60ffc7e3fc7fb 0xffd33f789a39f3f3

def z43 : W := mkw 0x4001cef64f204002 0x123fed4806ffb240 0xe001ffffffffc7c3 0xdfbfff7807fff3e0

def z44 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03f9fffffffff83f 0xdf3fff80e7fffc1c

def z45 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0039ff800ff9ff3c 0x1560c08066078f1f

def z46 : W := mkw 0x0001084000000000 0x0005000000480000 0x0000007ff0000001 0x080f000001f80000

def z47 : W := mkw 0x0000021002000000 0x0000040000112000 0x00000ffc7e3e0003 0x9e133f000239f000

def z48 : W := mkw 0x60c3cef65f2a414b 0xdf3fff5896fff2d2 0xe3c7ffffffffc7fb 0xffffff789ffff3f3

def z49 : W := mkw 0x13a1084000000003 0xf03ffbfbfe480000 0xfffffffff0000003 0xf83ffffffff80000

def z50 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x00060f8000380700 0x205020601a018303

def z51 : W := mkw 0x33e20210120a0149 0xed08ff12f8116092 0x03fe00000e3e0038 0xa640ff00f801f013

def z52 : W := mkw 0xe8c33bdd320be54b 0xddb716fd97796ff2 0xffc7fffffe3ffffb 0xffff3fff9ff9fff3

def z53 : W := mkw 0x13a1ce724f200003 0xf23ffffbfedfb000 0xfffffffffffe0003 0xfe3ffffffffff000

def z54 : W := mkw 0x1320000000000002 0x203de9a368000000 0x1c38000000000003 0x803fff8760000000

def z55 : W := mkw 0xa549586884448893 0xdd3d9816c7cc58b8 0xfff9ffffffc7f8ff 0xdfbfd89fe7fe7cfc

def z56 : W := mkw 0x0000000000000002 0x003700e900000000 0xfc00000000000003 0x403f00ff00000000

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c60f800e39c73a 0xf55020609a018313

def z58 : W := mkw 0x62d6a7941a9b536b 0xdd3276f8be33e7d7 0xe3fffffc7fffffff 0xfff3fff8fe3fffff

def z59 : W := mkw 0xe7def7bc9edfdbfb 0xdd3afefeffb7ffff 0xffffffffffffffff 0xffffffffffffffff

def z60 : W := mkw 0x00014a7247200002 0x123d8d0006dd3000 0x0001fffff0060003 0x1a3f1f0007f87000

def z61 : W := mkw 0x0214840008901220 0x0000600028028005 0x03fe00000ff8003c 0xa440e000f807801f

def z62 : W := mkw 0x00018e524b200002 0x12356500065ba000 0x00000ffc7e3e0003 0x9e133f000239f000

def z63 : W := mkw 0x0000423247200000 0x02088d0000953000 0x0000000000060000 0x02001f0000007000

def z64 : W := mkw 0x0080000000000001 0xc002125890000000 0xe3c6000000000003 0xe0133f7898000000

def z65 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe0f800e39c73b 0xf57ffffffa018313

def z66 : W := mkw 0x00018e524b200002 0x12356500065ba000 0x0001ff807ff80002 0x9433e700063f8000

def z67 : W := mkw 0xe5ca52bc964ec9d9 0xcd0a9e5ed1b57afa 0xfc00007ff00600c1 0x0a8f1f1f01f870e0

def z68 : W := mkw 0x2548402084440891 0xcd089812c0845098 0x03f800000fc6003c 0x8600d800e006701c

def z69 : W := mkw 0x480129c520016402 0x10b700e906680740 0x00000f8070000700 0x0013006002380300

def z70 : W := mkw 0x0000840008000002 0x1030600006028000 0x0001ff800ff80002 0x9430e00006078000

def z71 : W := mkw 0xc80139cd2001e400 0x008700ed01680f60 0xfc00007ff001ffc1 0x498f00ff01f80fe0

def z72 : W := mkw 0x00018e524b200000 0x12000400065ba000 0x00000f8070380000 0x0000000002398000

def z73 : W := mkw 0x60c20084100a4149 0xcd021258902042d2 0xe3c600000001c7f8 0x61c00078980003f3

def z74 : W := mkw 0xc800318d2001e400 0x008200ed01200f60 0xfc0000000001ffc0 0x418000ff00000fe0

def z75 : W := mkw 0xed4958eda444ec91 0xcd8f985fc1ec5af8 0xfff9f07fffc7f8ff 0xdfafd89fe5fe7cfc

def z76 : W := mkw 0x0000423006000000 0x00088c0000953000 0x0001fffffffe0003 0x9e3fff0007fff000

def z77 : W := mkw 0xe5ca52bc964ec9d9 0xcd0a9e5ed1b57afa 0xffffffffffffffff 0xffffffffffffffff

def z78 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fff0000ff8383c 0xa460e080fc078c1f

def z79 : W := mkw 0x60c20084100a4149 0xcd021258902042d2 0xe3c6007c0e07c7fb 0xffc01878980073f3

def z80 : W := mkw 0xa548d63acf648891 0xcf08fd16c197f8b8 0xfff9f07f8ffff8ff 0xdfacff9fe5c7fcfc

def z81 : W := mkw 0xc80139cd2001e400 0x1080000407680f60 0x0001fffff001ffc0 0x1980000007f80fe0

def z82 : W := mkw 0x1321ce724f200002 0x323deda36edfb000 0x1c39fffffffe0003 0x9e3fff8767fff000

def z83 : W := mkw 0x12a0000000000003 0xe03773f9b8000000 0xe3c6000000000003 0xe0133f7898000000

def z84 : W := mkw 0x12a0000000000002 0x203763e938000000 0xfc06000000000003 0x603f27ff18000000

def z85 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc00007f800600c1 0x0a8c181f01c070e0

def z86 : W := mkw 0x73e20294120a414b 0xed3ffffbf83162d2 0xfffe0ffc7e3fc7fb 0xfffffffffa39f3f3

def z87 : W := mkw 0x12a0000000000002 0x203763e938000000 0x0006000000000000 0x2013276018000000

def z88 : W := mkw 0xc80139cd2001e400 0x1080000407680f60 0xfc01fffff001ffc3 0x59ac009f07f80fe0

def z89 : W := mkw 0x275ce5208cd51ab3 0xdd38f8b2ee86d59d 0x03ffff800fffff3e 0xf770f8e0fe07ff1f

def z90 : W := mkw 0x73e3cef65f2a414b 0xff3ffffbfefff2d2 0xffffffffffffc7fb 0xfffffffffffff3f3

def z91 : W := mkw 0x73e20084100a414b 0xed3ffbfbf82042d2 0xfffe00000001c7fb 0xe1fffffff80003f3

def z92 : W := mkw 0x13a18e524b200003 0xf23ffffbfe5ba000 0xfffe0f8070380003 0xe03ffffffa398000

def z93 : W := mkw 0xc801ffff6f21e402 0x12bfeded07ffbf60 0xfc01ffffffffffc3 0xdfbfffff07ffffe0

def z94 : W := mkw 0xa448502884448890 0x0d000004018458b8 0x0001f07f8fc7f8fc 0x1f80000005c67cfc

def z95 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001f07ff1c60001 0x0a2fdf0005fe7000

def z96 : W := mkw 0xca14318d2091f620 0x008200ed29200f65 0xfffe00000001fffc 0x61c000fff8000fff

def z97 : W := mkw 0xa449de7acf648892 0x1f3ded0407dff8b8 0x0001fffffffff8ff 0x9fbfff0007fffcfc

def z98 : W := mkw 0x0001cc624d200002 0x123de90006ce9000 0x0001f00381c00000 0x002cc00005c60000

def z99 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0039ff800ff83806 0x9430e08066078c0c

def z100 : W := mkw 0xed49ffffef65ec93 0xdfbffdffc7fffff8 0xfff9ffffffffffff 0xdfbfffffe7fffffc

def z101 : W := mkw 0x000086124b200000 0x020065000013a000 0x0000000000380000 0x0000270000018000

def z102 : W := mkw 0x0100000000000001 0xc0089812c0000000 0xfff8000000000003 0xc02cd89fe0000000

def z103 : W := mkw 0xead7bfdd3a9bf76b 0xddb776fdbf7beff7 0xffffffffffffffff 0xffffffffffffffff

def z104 : W := mkw 0x2548402084440891 0xcd089812c0845098 0x0000000000060000 0x0200180000007000

def z105 : W := mkw 0x0214210000911220 0x000000a028000505 0x03fe00000001ff3c 0x614000e0f8000f1f

def z106 : W := mkw 0x11a0000000000003 0xe03ffb5bd0000000 0xfc00000000000003 0x803fff1f00000000

def z107 : W := mkw 0x9728502884448892 0x203de9a769841828 0x1c39f00381c03804 0x002cc08765c60c0c

def z108 : W := mkw 0xe8c31add320ae549 0xcd87165d91796af2 0xfc00007ff00600c1 0x0a8f1f1f01f870e0

def z109 : W := mkw 0x0214840008901222 0x103060002e028005 0x03ffff800ff8003e 0xb470e000fe07801f

def z110 : W := mkw 0x2040000000000001 0xcd00101080004090 0xe3c0007c0e07c0fb 0xdf801818800070f0

def z111 : W := mkw 0x33e0000000000003 0xed3ffbfbf8004090 0xfffe007c0e07c0fb 0xffbffffff80070f0

def z112 : W := mkw 0x0215ed624db11222 0x123de9a02ece9505 0x0039f00381c03804 0x002cc08065c60c0c

def z113 : W := mkw 0x00010a5243200000 0x0205050000592000 0x0000000070000000 0x0003070000380000

def z114 : W := mkw 0x0214e5200c911222 0x1038e8a02e869505 0x03ffffff8fffff3f 0xff7cf8e0ffc7ff1f

def z115 : W := mkw 0xa549de7acf648893 0xdf3dfd16c7dff8b8 0xfff9fffffffff8ff 0xdfbfff9fe7fffcfc

def z116 : W := mkw 0x60c30ad4120a414b 0xdd371658967962d2 0xe3c7fffffe3fc7fb 0xffff3f789ff9f3f3

def z117 : W := mkw 0x0015ef724fb11222 0x123ded0006dfb505 0x0001ffffffffff3f 0x9f7fff0007ffff1f

def z118 : W := mkw 0x0014a50008911220 0x1000000006028505 0x0001ff800ff9ff3c 0x1540000006078f1f

def z119 : W := mkw 0xc815bdcd2891f622 0x10b700ed076a8f65 0xfc01fffffff9ffff 0x5dff00ff07ff8fff

def z120 : W := mkw 0xb7e8502884448893 0xed3ffbfff98458b8 0xfffff07f8fc7f8ff 0xffbffffffdc67cfc

def z121 : W := mkw 0x0180000000000001 0xc00a9a5ad0000000 0xfffe000000000003 0xe03ffffff8000000

def z122 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc38000000000001 0x002fdf9f60000000

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000f800001c702 0x5110006002000300

def z124 : W := mkw 0xc000108c0000c000 0x0002004c01200a60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z125 : W := mkw 0xca0139cd2001e402 0x10b760ed2f680f60 0xfffffffff001ffc3 0xf9bfe0fffff80fe0

def z126 : W := mkw 0x1120000000000000 0x200d890340000000 0x1c00000000000000 0x000c000700000000

def z127 : W := mkw 0xc88139cd2001e403 0xd0b712fd97680f60 0xffc7fffff001ffc3 0xf9bf3fff9ff80fe0

def z128 : W := mkw 0x20c3ce725f2a014b 0xdf3dff1096dff092 0x03c7fffffffe003b 0xbe7fff009ffff013

def z129 : W := mkw 0x0000840008000002 0x1030600006028000 0x03c7ff800ff9c73a 0xf570e0609e078313

def z130 : W := mkw 0x00018e524b200002 0x12356500065ba000 0x00000f8070380000 0x0013270002398000

def z131 : W := mkw 0x13b4840008901223 0xe03ffbfbf8028005 0xfffe00000ff8003f 0xe47ffffff807801f

def z132 : W := mkw 0x1320000000000002 0x203de9a368000000 0x1c38000000000000 0x002cc08760000000

def z133 : W := mkw 0x6043cef65f2a414a 0x1f3ded0006fff2d2 0x0001ffffffffc7fb 0x9fffff0007fff3f3

def z134 : W := mkw 0x37e8402084440893 0xed3ffbfbf8845098 0xfffe00000fc6003f 0xe63ffffff806701c

def z135 : W := mkw 0x0015ef724fb11220 0x1200040006dfb505 0x0001ffffffffff3c 0x1f40000007ffff1f

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z137 : W := mkw 0xa549de7acf648891 0xdf089c16c7dff8b8 0xfff9fffffffff8ff 0xdfacd89fe7fffcfc

def z138 : W := mkw 0x0000840008000002 0x103de90006028000 0x0001ff800ff80003 0x943fff0006078000

def z139 : W := mkw 0xb5e8502884448891 0xed0f9b5fd18458b8 0xfff9f07f8fc7f8ff 0xdfafdf9fe5c67cfc

def z140 : W := mkw 0x10a0000000000000 0x2007034910000000 0x0000000000000000 0x0003070000000000

def z141 : W := mkw 0x8000100800008002 0x003700ed01000820 0xfc01f07f8001f8c3 0x59bf00ff05c00ce0

def z142 : W := mkw 0xec4979eda445ec92 0x1db700ed07ec5ff8 0xfc01ffffffc7ffff 0x5fbf00ff07fe7ffc

def z143 : W := mkw 0xd9a118cd2000e401 0xe08f9b5fd1680a60 0xfc00007ff00000c1 0x088f1f1f01f800e0

def z144 : W := mkw 0x00018e524b200002 0x12356500065ba000 0x0001fffff0380003 0x183f270007f98000

def z145 : W := mkw 0x0000021002000000 0x0000040000112000 0x03c60ffc7e3fc73b 0xff533f609a39f313

def z146 : W := mkw 0x8000100800008000 0x0000000401000820 0xfc01f07f8001f8c3 0x59ac009f05c00ce0

def z147 : W := mkw 0x2549ce72cf640893 0xdf3dfd12c6dff098 0x03f9fffffffe003f 0x9e3fff00e7fff01c

def z148 : W := mkw 0xca15ffff6fb1f622 0x12bfeded2fffbf65 0xffffffffffffffff 0xffffffffffffffff

def z149 : W := mkw 0x40820294120a4148 0x0002064810312242 0x00060f8070380700 0x205327601a398303

def z150 : W := mkw 0xc80118cd2000e402 0x10b7004d07680a60 0xfc01fffff00000c3 0x18bf001f07f800e0

def z151 : W := mkw 0x13a1cc624d200003 0xf23ffbfbfece9000 0xfffff00381c00003 0xe03ffffffdc60000

def z152 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0000000000000000 0x0000000000000000

def z153 : W := mkw 0x480129c520016400 0x1080000006680740 0x00000f8070000700 0x0000000002380300

def z154 : W := mkw 0x13b4a50008911223 0xf038fbb2fe028505 0x03ffff800ff9ff3e 0xf570ffe0fe078f1f

def z155 : W := mkw 0x13a0000000000002 0x203febeb78000000 0x1c3e000000000000 0x203fe7e778000000

def z156 : W := mkw 0x4000008400004000 0x0002004800200240 0xe0000ffc7001c7c3 0x59930078023803e0

def z157 : W := mkw 0x11a0000000000001 0xe002125bd0000000 0xfc00000000000000 0x0000001f00000000

def z158 : W := mkw 0xa448502884448890 0x0d000004018458b8 0x03f9f07f8fc7f8fe 0xdfa0c080e5c67cfc

def z159 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01f07ff00038c1 0x08af009f05f80ce0

def z160 : W := mkw 0x0200000000000002 0x003760e928000000 0xfffe000000000003 0xe03fe0fff8000000

def z161 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffffffe0000 0x1e2cc00007fff000

def z162 : W := mkw 0x0001ce724f200000 0x1200040006dfb000 0x0001fffffffe0000 0x1e00000007fff000

def z163 : W := mkw 0x1220000000000002 0x203561a128000000 0x0000000000000000 0x0000000000000000

def z164 : W := mkw 0xa548502884448891 0xcd001016c18458b8 0xfff9f07f8fc7f8fc 0x5f80009fe5c67cfc

def z165 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffff00001c03807 0xe03ffffffc060c0c

def z166 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc000ffff00007c1 0x089f007f03f803e0

def z167 : W := mkw 0x8000310800018002 0x103000a407000d20 0xfc01ffff8001ffc3 0x59bc00ff07c00fe0

def z168 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfff8000000000003 0xc02fdf9fe0000000

def z169 : W := mkw 0xec4979eda445ec90 0x1d80000407ec5ff8 0x0001ffffffc7fffc 0x1f80000007fe7ffc

def z170 : W := mkw 0x0000000000000000 0x000d890000000000 0x0000000000000001 0x000f1f0000000000

def z171 : W := mkw 0xa548100880448891 0xcd001016c10048b8 0xfff800000001f8fc 0x4180009fe0000cfc

def z172 : W := mkw 0x0001ce724f200000 0x120d8d0006dfb000 0x0001fffffffe0001 0x1e0f1f0007fff000

def z173 : W := mkw 0x62d6a7941a9b536b 0xdd3276f8be33e7d7 0xe3c60ffc7e3fc7fb 0xffd33f789a39f3f3

def z174 : W := mkw 0x8508502884448891 0xc0089816c1841828 0xfff9f00381c03807 0xc02cd89fe5c60c0c

def z175 : W := mkw 0xdaa139cd2001e402 0x30b763ed3f680f60 0xfc07fffff001ffc3 0x79bf27ff1ff80fe0

def z176 : W := mkw 0x60c20294120a4149 0xcd001610903162d2 0x03c60ffc7e3fc7f8 0xbfc03f009a39f3f3

def z177 : W := mkw 0xca1539cd2091f622 0x10b700ed2f680f65 0xfffffffff001ffff 0x79ff00fffff80fff

def z178 : W := mkw 0xa548100880448891 0xcd089816c10048b8 0xfff800000001f8ff 0xc1acd89fe0000cfc

def z179 : W := mkw 0x4000008400004000 0x0002004800200240 0xe00000000001c7c0 0x41800078000003e0

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001f0000fc1f83c 0x1500000004060c1c

def z181 : W := mkw 0x2548402084440891 0xcd089812c0845098 0x03f9f0000fc7f83e 0xd720d880e4067c1c

def z182 : W := mkw 0x60420294120a4148 0x0d020448003162d2 0xe0000ffc7e3fc7fb 0x5fd300780239f3f3

def z183 : W := mkw 0xc800318d2001e402 0x10b200ed07200f60 0xfc01ff800001ffc2 0x51b000ff06000fe0

def z184 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c6007c700600c3 0xea933f78983870e0

def z185 : W := mkw 0xa75dff7acff59ab3 0xdf3dfdb6efdffdbd 0xffffffffffffffff 0xffffffffffffffff

def z186 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x00000ffffe3e0003 0x9e1f3f0003f9f000

def z187 : W := mkw 0x0000840008000002 0x1030600006028000 0x00000f8000380000 0x0010200002018000

def z188 : W := mkw 0x0000210000010002 0x103000a006000500 0x0001ff800001ff02 0x513000e006000f00

def z189 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe000007c700600c1 0x0a831f18003870e0

def z190 : W := mkw 0x22d686101a9a1369 0xcd007610b813e097 0x03fe00000ffe003c 0xa640ff00f807f01f

def z191 : W := mkw 0x13a0000000000003 0xe038fbb2f8000000 0x03fe000000000002 0xe030ffe0f8000000

def z192 : W := mkw 0x1320000000000003 0xe03df9b3e8000000 0xfff8000000000003 0xc02cd89fe0000000

def z193 : W := mkw 0x0214c6324fb01220 0x0208ed002897b005 0x03fe00000ffe003c 0xa640ff00f807f01f

def z194 : W := mkw 0x0000021002000000 0x0000040000112000 0x00000ffc7e3e0000 0x1e0000000239f000

def z195 : W := mkw 0x8a15bd492891b622 0x10b560a52f4a8d25 0x1c39f00381c03804 0x002cc08765c60c0c

def z196 : W := mkw 0x0000000000000000 0x0008880000000000 0x0000000000000003 0x802cd80000000000

def z197 : W := mkw 0x0000c6324f200000 0x0208ed000097b000 0x000000000ffe0000 0x8600ff000007f000

def z198 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0039f00001c03804 0x0020c08064060c0c

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000007c0001c0c3 0x59800018000000e0

def z200 : W := mkw 0xc80118cd2000e402 0x00b700ed01680a60 0xfc00007ff00000c3 0x48bf00ff01f800e0

def z201 : W := mkw 0x00018c4249200002 0x12356100064a8000 0x0000000000000000 0x0000000000000000

def z202 : W := mkw 0x0001084000000002 0x1035000006480000 0x0001fffff0000003 0x183f000007f80000

def z203 : W := mkw 0x13b4210000911221 0xe00212fbf8000505 0xfffe00000001ff3c 0x614000fff8000f1f

def z204 : W := mkw 0x60420294120a4148 0x0d000400003162d2 0x0000007c700600c0 0x0a800000003870e0

def z205 : W := mkw 0x0100000000000000 0x0008880240000000 0x1c38000000000000 0x002cc08760000000

def z206 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0x0001fffff001ffc0 0x1993006007f80fe0

def z207 : W := mkw 0x871cf5288cd59ab2 0x1038e8a66f869d2d 0x1fffff838ff9ff3e 0xf57ce0e7ffc78f1f

def z208 : W := mkw 0x8508502884448890 0x0008880641841828 0x1ff9f0038fc1f83e 0xd52cc087e5c60c1c

def z209 : W := mkw 0x12b4a50008911222 0x303763e93e028505 0x03ffff800ff9ff3e 0xf573e7e0fe078f1f

def z210 : W := mkw 0x0001cc624d200002 0x123de90006ce9000 0x0001ff838ff80002 0x943ce00007c78000

def z211 : W := mkw 0xc800318d2001e400 0x0080000401200f60 0x000000000001ffc0 0x0180000000000fe0

def z212 : W := mkw 0x60c20084100a4149 0xcd021258902042d2 0xe3c600000001c7fb 0xe1d33f78980003f3

def z213 : W := mkw 0xca14b58d2891f622 0x10b260ed2f228f65 0xffffff800ff9fffe 0xf5f0e0fffe078fff

def z214 : W := mkw 0x871cf5288cd59ab2 0x1038e8a66f869d2d 0x1c39f00381c03804 0x002cc08765c60c0c

def z215 : W := mkw 0x13a0000000000001 0xe00ffb5bf8000000 0xfffe000000000001 0xa00fff1ff8000000

def z216 : W := mkw 0x0001294000010002 0x103500a006480500 0x0001fffff001ff03 0x593f00e007f80f00

def z217 : W := mkw 0xdba118cd2000e403 0xe0bffbfff9680a60 0xfffe007ff00000c3 0xe8bffffff9f800e0

def z218 : W := mkw 0xc800318d2001e402 0x00b700ed01200f60 0xfc0000000001ffc3 0x41bf00ff00000fe0

def z219 : W := mkw 0x0000402004000000 0x0008880000841000 0x0001f07f8fc60003 0x9e2cd80005c67000

def z220 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0001f07fffc60003 0x9e2fdf0005fe7000

def z221 : W := mkw 0x11a0000000000003 0xe03f9bfbd0000000 0xfc00000000000003 0x403f1fff00000000

def z222 : W := mkw 0x0000000000000000 0x0002004800000000 0xe000000000000003 0x4013007800000000

def z223 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03f9f0000fc1f83e 0xd520c080e4060c1c

def z224 : W := mkw 0x40820294120a4148 0x0002064810312242 0xe0060ffc7039c7c3 0x79d327781a3983e3

def z225 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c0007c7e07c0fb 0xdf831f18803870f0

def z226 : W := mkw 0xc80139cd2001e402 0x10b5000407680f60 0x0001fffff001ffc3 0x19bf000007f80fe0

def z227 : W := mkw 0x20c20000100a0149 0xcd00121090004092 0x03c6000000000038 0x2040000098000013

def z228 : W := mkw 0x0215ad4008911222 0x103560a02e4a8505 0x03fffffffff9ff3f 0xfd7fe0e0ffff8f1f

def z229 : W := mkw 0x0214a50008911220 0x000060a028028505 0x03fe00000ff9ff3c 0xe540e0e0f8078f1f

def z230 : W := mkw 0x13a0000000000003 0xe03712fbf8000000 0xfffe000000000003 0x603f00fff8000000

def z231 : W := mkw 0x2548402084440891 0xcd089812c0845098 0x03f9f07f8fc6003f 0x9e2cd800e5c6701c

def z232 : W := mkw 0x40820294120a4148 0x0002064810312242 0x0000000070000000 0x0003070000380000

def z233 : W := mkw 0x0000210000010002 0x103000a006000500 0x00000f8000000700 0x0010006002000300

def z234 : W := mkw 0xe44a52bc964ec9d8 0x0d00040401b57afa 0x0001fffffffffffc 0x1fc0000007ffffff

def z235 : W := mkw 0xedcb7bfdb64feddb 0xddbf9effd7fd7ffa 0xffffffffffffffff 0xffffffffffffffff

def z236 : W := mkw 0x60420084100a4148 0x0d000000002042d2 0x000000000001c7f8 0x01c00000000003f3

def z237 : W := mkw 0xa75cf5288cd59ab3 0xdd38f8b6ef86ddbd 0xffffffff8fffffff 0xfffcf8ffffc7ffff

def z238 : W := mkw 0x8000100800008000 0x0000000401000820 0xfff9f07f8fc1f8ff 0xddacc09fe5c60cfc

def z239 : W := mkw 0x20c20210120a0149 0xcd00161090116092 0x03c60f800e3fc73a 0xf7503f609a01f313

def z240 : W := mkw 0x0001ce724f200000 0x1208ed0006dfb000 0x0001fffffffe0000 0x9e00ff0007fff000

def z241 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001f0038ffe0000 0x862cff0005c7f000

def z242 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x00000f807ffe0000 0x8613ff00023ff000

def z243 : W := mkw 0x0000000000000000 0x0008e90000000000 0x0000000000000000 0x8000ff0000000000

def z244 : W := mkw 0x480129c520016402 0x10b700e906680740 0x0001fffff0000703 0x183f006007f80300

def z245 : W := mkw 0x0001ce724f200000 0x1200040006dfb000 0x0001fffffffe0003 0x9e133f0007fff000

def z246 : W := mkw 0x0215ef724fb11222 0x123064a02edfb505 0x03ffffffffffff3e 0xff70e0e0ffffff1f

def z247 : W := mkw 0xc801ffff6f21e402 0x12b704ed07ffbf60 0xfc01ffffffffffc3 0x5fbf00ff07ffffe0

def z248 : W := mkw 0x11a1ce724f200003 0xf23fff5bd6dfb000 0xfc01fffffffe0003 0x9e3fff1f07fff000

def z249 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0039fffffffe3807 0x9e3fff8067fffc0c

def z250 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fe0f800ff8073c 0xa450e060fa07831f

def z251 : W := mkw 0x0080000000000001 0xc002125890000000 0xe3c60f800e39c73b 0xf5533f789a018313

def z252 : W := mkw 0x12a0000000000000 0x200202e938000000 0x0006000000000000 0x2000006018000000

def z253 : W := mkw 0x880139492001a402 0x10b700ed07480d20 0xfc01f00380003803 0x403f00ff05c00c00

def z254 : W := mkw 0x0200210000010002 0x103060a02e000500 0x03ffff800001ff02 0xf130e0e0fe000f00

def z255 : W := mkw 0xdba139cd2001e403 0xf0bffbffff680f60 0xfffffffff001ffc3 0xf9bffffffff80fe0

def z256 : W := mkw 0xa548100880448891 0xcd001016c10048b8 0xfff9f0000fc1f8fe 0xd5a0c09fe4060cfc

def z257 : W := mkw 0x00014a7247200000 0x0200040000dd3000 0x0000007ff0060000 0x0a00000001f87000

def z258 : W := mkw 0x0200000000000002 0x003060a028000000 0x0038000000000000 0x0020c08060000000

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x0039f00001c03804 0x0020c08064060c0c

def z260 : W := mkw 0x0000021002000000 0x0000040000112000 0x000000000e3e0000 0x86003f000001f000

def z261 : W := mkw 0x0214210000911220 0x000000a028000505 0x03fe0f800e39ff3e 0xf55020e0fa018f1f

def z262 : W := mkw 0x60c38ed65b2a414b 0xdf377758967be2d2 0xe3c60ffc7e3fc7fb 0xffd33f789a39f3f3

def z263 : W := mkw 0xc801ffff6f21e400 0x1280040407ffbf60 0x0001ffffffffffc0 0x1f80000007ffffe0

def z264 : W := mkw 0x2040000000000001 0xcd00101080004090 0xe3f9f07c0fc7f8ff 0xdfa0d898e4067cfc

def z265 : W := mkw 0x1320000000000002 0x203de9a368000000 0x1ffe000000000002 0xe03ce0e7f8000000

def z266 : W := mkw 0xc815bdcd2891f620 0x10800004076a8f65 0x0001fffffff9fffc 0x1dc0000007ff8fff

def z267 : W := mkw 0xe8c2318d300be549 0xcd8212fd91204ff2 0xffc600000001fff8 0x61c000ff98000ff3

def z268 : W := mkw 0xed48318da045ec91 0xcd8210ffc1204ff8 0xfff800000001fffc 0x418000ffe0000ffc

def z269 : W := mkw 0x13b4210000911223 0xe03ffbfbf8000505 0xfffe00000001ff3f 0xe17ffffff8000f1f

def z270 : W := mkw 0xa448502884448890 0x0d000004018458b8 0x0000007f800600c0 0x0a80000001c070e0

def z271 : W := mkw 0x52a20294120a414a 0x203767e938312242 0x00060f8070380700 0x205327601a398303

def z272 : W := mkw 0x0001084000000002 0x103de90006480000 0x0001fffff0000003 0x983fff0007f80000

def z273 : W := mkw 0x60c20084100a4149 0xcd021258902042d2 0xe3c60f800e39c7fa 0xf5d020789a0183f3

def z274 : W := mkw 0x1320000000000000 0x200000a368000000 0x1c38000000000000 0x0000008760000000

def z275 : W := mkw 0x13a0000000000001 0xe00a9afbf8000000 0xfffe000000000003 0xe02cd8fff8000000

def z276 : W := mkw 0x20c20210120a0149 0xcd00161090116092 0x0000000000060000 0x02001f0000007000

def z277 : W := mkw 0x12a18e524b200002 0x323767e93e5ba000 0x00060f8070380000 0x201327601a398000

def z278 : W := mkw 0xa548100880448891 0xcd001016c10048b8 0xfff8007c0e07f8ff 0xdf80189fe0007cfc

def z279 : W := mkw 0x53a0008400004003 0xe03ffbfbf8200240 0xfffe0ffc7001c7c3 0xf9bffffffa3803e0

def z280 : W := mkw 0xef5dfdedacd5feb3 0xddbff8ffefeedffd 0xffffffffffffffff 0xfffff8ffffffffff

def z281 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x00000ffff03e0001 0x0a1f3f0003f9f000

def z282 : W := mkw 0x37e8402084440891 0xed08fb12f8845098 0x03fe00000fc6003c 0xa600ff00f806701c

def z283 : W := mkw 0x13a0402004000003 0xe03ffbfbf8841000 0xfffff07f8fc60003 0xfe3ffffffdc67000

def z284 : W := mkw 0x13a0000000000003 0xe03773fbf8000000 0xfffe000000000000 0x601327fff8000000

def z285 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc000ffff001c7c3 0x599f007f03f803e0

def z286 : W := mkw 0x62d686941a9a5369 0xcd027658b833e2d7 0xe3fe0ffc7fffc7ff 0xffd3ff78fa3ff3ff

def z287 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001ff83f1f80000 0x003fe70007ff8000

def z288 : W := mkw 0x13a0000000000003 0xe03272fbf8000000 0xfffe000000000002 0xe030e0fff8000000

def z289 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01f0038001ffc0 0x41ac00ff05c00fe0

def z290 : W := mkw 0xdba0318d2001e401 0xe08212fff9200f60 0xfffe00000001ffc0 0x618000fff8000fe0

def z291 : W := mkw 0xad497969a445ac93 0xddbd98b7c7cc5db8 0xfff9f07f8fc7f8ff 0xdfacd89fe5c67cfc

def z292 : W := mkw 0x60c20084100a4149 0xcd021258902042d2 0xe0000000000000c0 0x00800018000000e0

def z293 : W := mkw 0x0201ce724f200002 0x123deda02edfb000 0x03fffffffffe0003 0xfe3fffe0fffff000

def z294 : W := mkw 0x0000000000000000 0x0007004900000000 0xfc00000000000001 0x000f001f00000000

def z295 : W := mkw 0x880118492000a400 0x0085000501480820 0x1c00000380000000 0x000c000701c00000

def z296 : W := mkw 0x00010a5002000002 0x1035040006592000 0x0001fffffe3e0003 0x9e3f3f0007f9f000

def z297 : W := mkw 0x0000000000000002 0x003000a000000000 0x0000000000000002 0x403000e000000000

def z298 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000000 0x602cc0fff8000000

def z299 : W := mkw 0x60c242b4160a4149 0xcd0a9e5890b572d2 0xe3c7ffffffffc7fb 0xffffff789ffff3f3

def z300 : W := mkw 0xa449de7acf648890 0x1f00040407dff8b8 0x0001fffffffff8fc 0x1f80000007fffcfc

def z301 : W := mkw 0x8509dc6acd648892 0x123de90647ce9828 0x1c39f00381c03804 0x002cc08765c60c0c

def z302 : W := mkw 0x00014a7247200002 0x023ded0000dd3000 0x0000007ff0060003 0x8a3fff0001f87000

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001f0000001f802 0x5120008004000c00

def z304 : W := mkw 0xe5ca52bc964ec9d9 0xcd0a9e5ed1b57afa 0xffc60ffffe3fc7fb 0xffdf3f7f9bf9f3f3

def z305 : W := mkw 0x2548402084440891 0xcd089812c0845098 0xe3f8007c0fc7c0ff 0xdf80d818e00670fc

def z306 : W := mkw 0xed4979eda445ec91 0xdd889816c7ec5ff8 0xfff9ffffffc7ffff 0xdfacd89fe7fe7ffc

def z307 : W := mkw 0x0508402084440890 0x0008880240841008 0x0038000001c00004 0x0000c0006006000c

def z308 : W := mkw 0x0214210000911220 0x000000a028000505 0x0006000000000700 0x2040006018000303

def z309 : W := mkw 0x00018c4008000002 0x10356000064a8000 0x0001fffffff80003 0x9c3fe00007ff8000

def z310 : W := mkw 0xc801deff6f20e402 0x12bfed4d07ffba60 0xfc01fffffffe00c3 0x9ebfff1f07fff0e0

def z311 : W := mkw 0x480129c520016402 0x10b700e906680740 0xe0000ffc7001c7c3 0x59930078023803e0

def z312 : W := mkw 0x2040021002000001 0xcd00141080116090 0xe3c00ffc7e3fc0fb 0xdf933f188239f0f0

def z313 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc39fffff1c1ffc7 0x59bfc0ff67fe0fec

def z314 : W := mkw 0xe8c31add320ae549 0xcd87165d91796af2 0xffc60ffffe3fc7fb 0xffdf3f7f9bf9f3f3

def z315 : W := mkw 0xc800318d2001e400 0x008200ed01200f60 0xfc01f07f8001ffc3 0x59ac00ff05c00fe0

def z316 : W := mkw 0xc90139cd2001e403 0xd0bf98ffc7680f60 0xfff9fffff001ffc3 0xd9bfd8ffe7f80fe0

def z317 : W := mkw 0x12a1ce724f200002 0x323fefe93edfb000 0x0007fffffffe0003 0xbe3fff601ffff000

def z318 : W := mkw 0xa65cf5288cd59ab2 0x1d3060a42f86ddbd 0x03ffffff8ffffffe 0xfff0e0e0ffc7ffff

def z319 : W := mkw 0x4000008400004000 0x0002004800200240 0x00000f8070000700 0x0013006002380300

def z320 : W := mkw 0x4a15adc528917622 0x10b760e92e6a8745 0x03ffff807ff9ff3e 0xf573e0e0fe3f8f1f

def z321 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c60ffc7e3fc7f8 0x7fc000789a39f3f3

def z322 : W := mkw 0x0100000000000001 0xc0089812c0000000 0xfc00000000000001 0x000c181f00000000

def z323 : W := mkw 0xe54a52bc964ec9d9 0xcd089c16c1b57afa 0xfff9ffffffffffff 0xdfecd89fe7ffffff

def z324 : W := mkw 0xca15bdcd2891f622 0x10b060a42f6a8f65 0x03fffffffff9fffe 0xfdf0e0e0ffff8fff

def z325 : W := mkw 0x0214840008901222 0x003060a028028005 0x03fe00000ff8003e 0xe470e0e0f807801f

def z326 : W := mkw 0x0080000000000001 0xc002125890000000 0xe000000000000001 0x00031f1800000000

def z327 : W := mkw 0x8000100800008000 0x0000000401000820 0xfc00007f800000c1 0x088c001f01c000e0

def z328 : W := mkw 0x0001cc624d200000 0x1200000006ce9000 0x0001f00381c00000 0x0000000005c60000

def z329 : W := mkw 0x0214840008901220 0x0000600028028005 0x0038000001c00004 0x0000c0006006000c

def z330 : W := mkw 0x0001ef724f210002 0x123deda006dfb500 0x0001ffffffffff03 0xdf3fffe007ffff00

def z331 : W := mkw 0x25ca4230964e09d9 0xcd089e12d095709a 0x03fe00000ffe003c 0xa640ff00f807f01f

def z332 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe0060ffc703e07c1 0x2ad33f781a39f3e3

def z333 : W := mkw 0x0014a50008911222 0x103000a006028505 0x0001ff800ff9ff3e 0x557000e006078f1f

def z334 : W := mkw 0xa448502884448890 0x0d000004018458b8 0xfc01f07f8fc7f8ff 0x5fac009f05c67cfc

def z335 : W := mkw 0x8d097969a445ac92 0x10bd88a747cc1d28 0x1c39f00381c03804 0x002cc08765c60c0c

def z336 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0007ff800039ff02 0x717020e01e018f03

def z337 : W := mkw 0x0000210000010002 0x103000a006000500 0x03f9ff800fc1ff3e 0xd530c0e0e6060f1c

def z338 : W := mkw 0x13a0000000000003 0xe03dfb12f8000000 0x03fe000000000003 0xa03fff00f8000000

def z339 : W := mkw 0x0000000000000000 0x0000000000000000 0x03f800000fc0003c 0x8400c000e006001c

def z340 : W := mkw 0x40820294120a4149 0xc002165890312242 0xe3c60f8070380703 0xe0533f789a398303

def z341 : W := mkw 0xe5cbdefedf6ec9db 0xdf3fff5ed7fffafa 0xffffffffffffffff 0xffffffffffffffff

def z342 : W := mkw 0x0215ce724fb01222 0x123ded002edfb005 0x03fffffffffe003f 0xbe7fff00fffff01f

def z343 : W := mkw 0xe84139cd2001e403 0xddb710fd87684ff0 0xffc1fffffe07fffb 0xdfbf18ff87f87ff0

def z344 : W := mkw 0xa75cb50888d59ab3 0xdd3070b6ef02cdbd 0xffffff800ff9fffe 0xf5f0e0fffe078fff

def z345 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xffc7fffffe39fffb 0xfdff20ff9ff98ff3

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c600000001c738 0x6140006098000313

def z347 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc01f07f8fc600c3 0x9eacd81f05c670e0

def z348 : W := mkw 0x4000008400004000 0x0002004800200240 0xe3c60ffc7e39c7fb 0xfdd320789a3983f3

def z349 : W := mkw 0x0000000000000001 0xc000101080000000 0xe3c0000000000003 0xc000181880000000

def z350 : W := mkw 0x4080008400004001 0xc002125890200240 0xe3c60ffc7001c7c3 0xf9933f789a3803e0

def z351 : W := mkw 0x93a0100800008003 0xe03ffbfff9000820 0xfffff07f8001f8c3 0xf9bffffffdc00ce0

def z352 : W := mkw 0x400108c400004002 0x1037004806680240 0xe001fffff001c7c3 0x59bf007807f803e0

def z353 : W := mkw 0x0214210000911220 0x000000a028000505 0x03fff0000fc1ff3e 0xf560c0e0fc060f1f

def z354 : W := mkw 0x0014a50008911220 0x1000000006028505 0x0001f00001c03804 0x0000000004060c0c

def z355 : W := mkw 0x40020294120a4148 0x0000040000312242 0x00000f8070380700 0x0040000002398303

def z356 : W := mkw 0x0214210000911222 0x003060a028000505 0x03fe00000001ff3e 0xe170e0e0f8000f1f

def z357 : W := mkw 0x73e20294120a414b 0xed3ffffbf83162d2 0xfffe007c700600c3 0xeabffffff83870e0

def z358 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffe0f8000380703 0xe07ffffffa018303

def z359 : W := mkw 0x71e20294120a4149 0xed0f9f5bd03162d2 0xfc00007c700600c1 0x0a8f1f1f003870e0

def z360 : W := mkw 0x8000502804008000 0x0008880401841820 0xfc01f07f8fc7f8c3 0xdfacd89f05c67ce0

def z361 : W := mkw 0x60c34af6572a4149 0xcf0f9f5890fd72d2 0xe3c60ffffe3fc7fb 0xffdf3f789bf9f3f3

def z362 : W := mkw 0xa5495a7ac7648891 0xcf0d9d16c1dd78b8 0xfff9f07fffc7f8ff 0xdfafdf9fe5fe7cfc

def z363 : W := mkw 0xc80139cd2001e402 0x10bfe9ed07680f60 0xfc01fffff001ffc3 0xd9bfffff07f80fe0

def z364 : W := mkw 0xc800318d2001e400 0x008200ed01200f60 0xfc000ffc7001ffc3 0x599300ff02380fe0

def z365 : W := mkw 0x4000008400004000 0x0000000000200240 0x00000ffc7001c7c0 0x19800000023803e0

def z366 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff8007f800600c3 0xcaacd89fe1c070e0

def z367 : W := mkw 0x8000100800008000 0x0000000401000820 0x1c01f00380003800 0x002c008705c00c00

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c000000e01c03a 0xd500000080000010

def z369 : W := mkw 0xb768502884448893 0xed3df9b7e98458b8 0xfff9f07f8fc7f8ff 0xdfacd89fe5c67cfc

def z370 : W := mkw 0x53a20294120a414b 0xe03ffffbf8312242 0xfffe0f8070380703 0xe07ffffffa398303

def z371 : W := mkw 0xa45cf5288cd59ab0 0x1d0000040786ddbd 0x0001ffff8ffffffc 0x1fc0000007c7ffff

def z372 : W := mkw 0x8801ff7b6f21a402 0x12bdeda507dfbd20 0x1c01fffffffe3803 0x9e3fff8707fffc00

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c6000000000002 0xe010206098000000

def z374 : W := mkw 0x000086100a000002 0x103064000613a000 0x0001fffc7ffe0003 0x9e33ff00063ff000

def z375 : W := mkw 0x13a0000000000001 0xe00f9bfbf8000000 0xfffe000000000001 0x600f1ffff8000000

def z376 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc39f07f81c638c5 0x0aacd89f65c67cec

def z377 : W := mkw 0x4000008400004000 0x0002004800200240 0xe000007c700000c1 0x08830018003800e0

def z378 : W := mkw 0x480129c520016402 0x10b700e906680740 0x0001ff807001ff02 0x513300e006380f00

def z379 : W := mkw 0xe5ca108c904ec9d9 0xcd02125ed1204afa 0xfffe00000001fffc 0x61c000fff8000fff

def z380 : W := mkw 0x0100000000000003 0xc03df912c0000000 0xfff8000000000003 0xc03fff9fe0000000

def z381 : W := mkw 0x0000000000000002 0x003fe9e900000000 0xfc00000000000003 0xc03fffff00000000

def z382 : W := mkw 0xc80139cd2001e402 0x10b500a507680f60 0x1c01fffff001ffc0 0x19ac008707f80fe0

def z383 : W := mkw 0x00018e524b200002 0x123ded00065ba000 0x00000f8070380003 0x803fff0002398000

def z384 : W := mkw 0x5ba129c520016403 0xf0bffbfbfe680740 0xfffe0f8070000703 0xe03ffffffa380300

def z385 : W := mkw 0xed4979eda445ec93 0xddbf98ffc7ec5ff8 0xfc01fffff007ffc3 0x5bbf18ff07f87fe0

def z386 : W := mkw 0x0000402004000000 0x0000000000841000 0x0001f07f8fc60000 0x1e00000005c67000

def z387 : W := mkw 0xc80118cd2000e400 0x0080000401680a60 0x0000007ff00000c0 0x0880000001f800e0

def z388 : W := mkw 0x0080000000000003 0xc03712f990000000 0xffc6000000000003 0xe03f3fff98000000

def z389 : W := mkw 0x13a0000000000001 0xe00afbfbf8000000 0xfffe000000000000 0xe000fffff8000000

def z390 : W := mkw 0x0001ce724f200000 0x12088c0006dfb000 0x0001fffffffe0003 0x9e2cd80007fff000

def z391 : W := mkw 0x4296a7941a9b536a 0x103266e83e33a747 0x03ffff807ff9ff3e 0xf573e7e0fe3f8f1f

def z392 : W := mkw 0x0000021002000000 0x0000040000112000 0x0000007c70060001 0x0a031f0000387000

def z393 : W := mkw 0x6043cef65f2a4148 0x1f00040006fff2d2 0x0001ffffffffc7f8 0x1fc0000007fff3f3

def z394 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c60f807039c7f8 0x61d327789a3983f3

def z395 : W := mkw 0x60c2c6b65f2a4149 0xcf0aff5890b7f2d2 0xe3c60ffc7fffc7fb 0xffd3ff789a3ff3f3

def z396 : W := mkw 0x1334a50008911222 0x303de9a36e028505 0x1fffff800ff9ff3e 0xf57ce0e7fe078f1f

def z397 : W := mkw 0x13b4a50008911223 0xf03272fbfe028505 0xffffff800ff9ff3e 0xf570e0fffe078f1f

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000f800e39c738 0x1540000002018313

def z399 : W := mkw 0xe8c33bdd320be549 0xdd82165c97796ff2 0xe3c7fffffe3ffffb 0xffd33f789ff9fff3

def z400 : W := mkw 0xc801bdcd2801e402 0x10b760ed076a8f60 0xfc01fffffff9ffc3 0xddbfe0ff07ff8fe0

def z401 : W := mkw 0xc8017bff6721e402 0x12bf8ded07fd3f60 0xfc01fffff007ffc3 0x5bbf1fff07f87fe0

def z402 : W := mkw 0xa5c8502884448891 0xcd0a9a5ed18458b8 0xfffff07f8fc7f8ff 0xffbffffffdc67cfc

def z403 : W := mkw 0xa548502884448890 0x0d088806418458b8 0x1c39f07f8fc7f8fc 0x1facc08765c67cfc

def z404 : W := mkw 0x2041ce724f200003 0xdf3dfd1086dff090 0xe3c1ffffffffc0fb 0xdfbfff1887fff0f0

def z405 : W := mkw 0x0200840008000002 0x103060a02e028000 0x03ffff800ff80002 0xf430e0e0fe078000

def z406 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xffffffff8fffffff 0xfffcf8ffffc7ffff

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x00060f8000380700 0x205020601a018303

def z408 : W := mkw 0x6056a7941a9b5368 0x1d0004000633e7d7 0x0001fffc7ffffffc 0x1fc00000063fffff

def z409 : W := mkw 0x0000c6324f200002 0x023ded000097b000 0x000000000ffe0003 0x863fff000007f000

def z410 : W := mkw 0x0000c6324f200000 0x0208ed000097b000 0x00000ffc7ffe0003 0x9e13ff00023ff000

def z411 : W := mkw 0x0000c6324f200000 0x0208ed000097b000 0x0001f07f8ffe0003 0x9e2cff0005c7f000

def z412 : W := mkw 0xdba139cd2001e403 0xf0b712ffff680f60 0xfffffffff001ffc3 0x79bf00fffff80fe0

def z413 : W := mkw 0x13a0c6324f200003 0xe23ffffbf897b000 0xfffe00000ffe0003 0xe63ffffff807f000

def z414 : W := mkw 0x2040000000000001 0xcd00101080004090 0xe000007c000600c1 0x0a801818000070e0

def z415 : W := mkw 0xe8c2339d320be549 0xcd8216fd91316ff2 0xffc60ffc7e3ffffb 0xffd33fff9a39fff3

def z416 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03c7ffffffffc73b 0xff7fff609ffff313

def z417 : W := mkw 0x0214a50008911220 0x100060002e028505 0x03ffff800ff9ff3c 0xb540e000fe078f1f

def z418 : W := mkw 0xa548523886448891 0xcd089c16c19578b8 0xfff9fffffffff8ff 0xdfbfff9fe7fffcfc

def z419 : W := mkw 0xe8c339cd300be54b 0xddb712fd97684ff2 0xffc7fffff001fffb 0x79ff00ff9ff80ff3

def z420 : W := mkw 0x13a14a7247200003 0xe23ffffbf8dd3000 0xfffe007ff0060003 0xea3ffffff9f87000

def z421 : W := mkw 0x0214210000911222 0x103000a02e000505 0x03ffff800001ff3e 0x717000e0fe000f1f

def z422 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0007fffffffe0703 0xbe7fff601ffff303

def z423 : W := mkw 0x73e20294120a4149 0xed0aff5af83162d2 0xe3fe0ffc7e3fc7fb 0xffd3ff78fa39f3f3

def z424 : W := mkw 0x8214b50808919222 0x103060a42f028d25 0xffffffff8ff9ffff 0xfdfce0ffffc78fff

def z425 : W := mkw 0x0000000000000002 0x0030600000000000 0x0000000000000002 0x8030e00000000000

def z426 : W := mkw 0x0000000000000002 0x1030000006000000 0x0001ff8000000002 0x1030000006000000

def z427 : W := mkw 0x0000210000010000 0x1000000006000500 0x0001ff800001ff00 0x1100000006000f00

def z428 : W := mkw 0x9ba139492001a403 0xf0bffbffff480d20 0xfffff00380003803 0xe03ffffffdc00c00

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000f800e380002 0x9410200002018000

def z430 : W := mkw 0x0001486245200000 0x020d890000cc1000 0x0000000380000000 0x000c000001c00000

def z431 : W := mkw 0x13a0000000000003 0xe03dfbb3f8000000 0x1ffe000000000000 0xa02cff87f8000000

def z432 : W := mkw 0x0014840008901220 0x0000000000028005 0x000000000ff8003c 0x044000000007801f

def z433 : W := mkw 0x0214840008901220 0x0000600028028005 0x0006000000380000 0x2040200018018003

def z434 : W := mkw 0xa548d4288c448893 0xdd38f816c786d8b8 0xfff9ffff8ffff8ff 0xdfbcf89fe7c7fcfc

def z435 : W := mkw 0x71e20294120a4149 0xed0f9f5bd03162d2 0xffc60ffc7e3fc7fb 0xffdf3f7f9a39f3f3

def z436 : W := mkw 0xd9a139cd2001e403 0xf0bf9bffd7680f60 0xfc01fffff001ffc3 0x59bf1fff07f80fe0

def z437 : W := mkw 0xa448502884448891 0xcd001014818458b8 0xe3c1f07f8fc7f8ff 0xdf80181885c67cfc

def z438 : W := mkw 0x880139492001a402 0x10b500a507480d20 0x1c01fffff0003803 0x183f008707f80c00

def z439 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffff0000fc1f83f 0xf53ffffffc060c1c

def z440 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c6007c7007c7f9 0x6bc31f78983873f3

def z441 : W := mkw 0x20420210120a0148 0x0d00040000116092 0x000000000e3e0038 0x064000000001f013

def z442 : W := mkw 0x60420294120a4148 0x0d000400003162d2 0x03c60ffc7e3fc7fa 0xffd020609a39f3f3

def z443 : W := mkw 0x0000840008000002 0x1030600006028000 0x0001f00001c00000 0x0020c00004060000

def z444 : W := mkw 0x62d62394129b5369 0xcd0216f8b83167d7 0xe3fe0ffc7e3fffff 0xffd33ff8fa39ffff

def z445 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0007ff800ff80702 0xb470e0601e078303

def z446 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff800000fc7f8fc 0xc780d89fe0067cfc

def z447 : W := mkw 0x0300000000000003 0xc038f8b2e8000000 0xfffe000000000003 0xe03cf8fff8000000

def z448 : W := mkw 0x11a0000000000001 0xe0089b12d0000000 0x0000000000000000 0x00001f0000000000

def z449 : W := mkw 0x0001ce724f200002 0x123fede906dfb000 0xfc01fffffffe0003 0xde3fffff07fff000

def z450 : W := mkw 0x0000840008000000 0x1000000006028000 0x0001ff800ff80000 0x1400000006078000

def z451 : W := mkw 0x0000840008000000 0x0000600000028000 0x000000000ff80000 0x8400e00000078000

def z452 : W := mkw 0x0001ce724f200002 0x1230640006dfb000 0x0001fffffffe0002 0x9e30e00007fff000

def z453 : W := mkw 0x0000c4200c000002 0x1038e80006869000 0x0001ffff8ffe0003 0x9e3cf80007c7f000

def z454 : W := mkw 0x4a15adc528917622 0x10b760e92e6a8745 0x00060f8070380700 0x205320601a398303

def z455 : W := mkw 0x2040000000000000 0x0d00000000004090 0x0000007c0e07c0f8 0x1f800000000070f0

def z456 : W := mkw 0x73f6a7941a9b536b 0xfd3ffffbfe33e7d7 0xfffffffc7fffffff 0xfffffffffe3fffff

def z457 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xffc0007f8e07c0fb 0xdf8c181f81c070f0

def z458 : W := mkw 0x0100000000000003 0xc03f98fbc0000000 0xfff8000000000003 0xc03fd8ffe0000000

def z459 : W := mkw 0x2040402004000001 0xcd08981080845090 0xe3c1f07f8fc7c0fb 0xdfacd81885c670f0

def z460 : W := mkw 0x0280000000000003 0xc03272f8b8000000 0xe3fe000000000003 0xe033fff8f8000000

def z461 : W := mkw 0x0000c6324f200002 0x1238ed000697b000 0x0001ff800ffe0002 0x9630ff000607f000

def z462 : W := mkw 0x60c20294120a414b 0xcd3fff58903162d2 0xe3c60ffc7e3fc7fb 0xffffff789a39f3f3

def z463 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fe0f8000380702 0xe070e0e0fa018303

def z464 : W := mkw 0xc801ffff6f21e402 0x12bded0407ffbf60 0x0001ffffffffffc3 0x9fbfff0007ffffe0

def z465 : W := mkw 0x0001cc624d200002 0x123de90006ce9000 0x0001f07f8fc60003 0x9e2cd80005c67000

def z466 : W := mkw 0x0200000000000002 0x003de9a028000000 0x03fe000000000003 0xe03fffe0f8000000

def z467 : W := mkw 0x0014210000911220 0x0000000000000505 0x000000000001ff3c 0x0140000000000f1f

def z468 : W := mkw 0x13a0000000000001 0xe0001212f8000000 0x03fe000000000000 0x20000000f8000000

def z469 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc01f07f8fc7f8fd 0x1f8c181f05c67cfc

def z470 : W := mkw 0x2040000000000001 0xcd00101080004090 0xe3c000000001c0f8 0x41800018800000f0

def z471 : W := mkw 0x8508502884448890 0x0008880641841828 0xfc39f07f81c1f8c7 0x59acc09f65c60cec

def z472 : W := mkw 0x8508502884448890 0x0008880641841828 0x1c39f07f8fc63807 0x9e2cd88765c67c0c

def z473 : W := mkw 0x0000c4224d200000 0x0208e90000869000 0x0000000001c00000 0x0000c00000060000

def z474 : W := mkw 0x0000840008000002 0x1030600006028000 0x03f9ff800ff9f83e 0xd530e080e6078c1c

def z475 : W := mkw 0x0214840008901220 0x0000600028028005 0x03fff0000ff9f83e 0xf560e080fc078c1f

def z476 : W := mkw 0x68c32bd5320b654b 0xddb716f9967967d2 0xe3c60ffc7e3fc7fb 0xffd33f789a39f3f3

def z477 : W := mkw 0x0000021002000000 0x0000040000112000 0x00000f8070380000 0x0013270002398000

def z478 : W := mkw 0xdba0318d2001e403 0xe0bffbfff9200f60 0xfffe00000001ffc3 0xe1bffffff8000fe0

def z479 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff8007f8007f8fd 0x4b8c189fe1c07cfc

def z480 : W := mkw 0x73e20294120a4149 0xed0216fbf83162d2 0xfffe0ffc7e3fc7fb 0xffd33ffffa39f3f3

def z481 : W := mkw 0xe8433bdd320be548 0x1d80040407796ff2 0x0001fffffe3ffff8 0x1fc0000007f9fff3

def z482 : W := mkw 0x0080000000000001 0xc002125890000000 0xe3c6000000000000 0x6000007898000000

def z483 : W := mkw 0xb7fcf5288cd59ab3 0xfd3ffbffff86ddbd 0xffffffff8fffffff 0xffffffffffc7ffff

def z484 : W := mkw 0x6040008400004001 0xcd021058802042d0 0xe3c00ffc7e07c7fb 0xdf931878823873f0

def z485 : W := mkw 0xa748502884448893 0xcd38f8b6e98458b8 0xfffff07f8fc7f8ff 0xffbcf8fffdc67cfc

def z486 : W := mkw 0x880031092001a400 0x008000a501000d20 0x1c00000000003800 0x0000008700000c00

def z487 : W := mkw 0x40820294120a4148 0x0002064810312242 0x00060ffc7e3e0703 0xbe533f601a39f303

def z488 : W := mkw 0x480108c520006400 0x0087004900680240 0x0000000070000000 0x0003000000380000

def z489 : W := mkw 0xc801bfdf6b21e402 0x12b765ed077baf60 0xfc01fffff039ffc3 0x59bf27ff07f98fe0

def z490 : W := mkw 0x13a0000000000001 0xe008fb12f8000000 0xfffe000000000003 0xe02cff9ff8000000

def z491 : W := mkw 0x60c20084100a4149 0xcd021258902042d2 0xe3c60ffc7001c7fb 0x79d300789a3803f3

def z492 : W := mkw 0x0001ce724f200000 0x020ded0000dfb000 0x0000007ffffe0001 0x8e0fff0001fff000

def z493 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0x03f9f07f8fc7f8fc 0x9f80d800e5c67cfc

def z494 : W := mkw 0x0801294120012402 0x10b500a106480500 0x0000000000000000 0x0000000000000000

def z495 : W := mkw 0x8000100800008000 0x0000000401000820 0xfc0000000001f8c0 0x4180009f00000ce0

def z496 : W := mkw 0xe8c33bdd320be54b 0xddb716fd97796ff2 0xfc01fffff007ffc3 0x5bbf1fff07f87fe0

def z497 : W := mkw 0x880139492001a402 0x10b500a507480d20 0x1c01ff838001ff02 0x513c00e707c00f00

def z498 : W := mkw 0xb7e8100880448891 0xed0212fff90048b8 0xfffe00000001f8fc 0x618000fff8000cfc

def z499 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc000f807001ffc0 0x419300ff02380fe0

def z500 : W := mkw 0xed4871ada445ec91 0xcd8a98ffc1a45ff8 0xfff9f07f8fc7ffff 0xdfacd8ffe5c67ffc

def z501 : W := mkw 0x0100000000000001 0xc0089812c0000000 0xfff9f0000fc1f83f 0xd52cd89fe4060c1c

def z502 : W := mkw 0x0000000000000002 0x003500a100000000 0x1c00000000000000 0x002c008700000000

def z503 : W := mkw 0x12a0000000000000 0x2000630038000000 0x0006000000000000 0x2000270018000000

def z504 : W := mkw 0xb7e8100880448893 0xed3ffbfff90048b8 0xfffe00000001f8ff 0xe1bffffff8000cfc

def z505 : W := mkw 0x0000000000000002 0x003700e900000000 0x0000000000000000 0x0013006000000000

def z506 : W := mkw 0x0214e7324fb11222 0x1238eda02e97b505 0x03ffff800fffff3e 0xf770ffe0fe07ff1f

def z507 : W := mkw 0x0200000000000002 0x003060a028000000 0x03fe0f800e39c73a 0xf570e0e0fa018313

def z508 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc01f07ff001f8c3 0x59af009f05f80ce0

def z509 : W := mkw 0x0081ce724f200003 0xd23fff5896dfb000 0xe3c7fffffffe0003 0xfe3fff789ffff000

def z510 : W := mkw 0xb5e8502884448891 0xed0f9b5fd18458b8 0xfc00007f800600c1 0x0a8f1f1f01c070e0

def z511 : W := mkw 0xa040100800008001 0xcd001014810048b0 0xffc1f07f8e07f8fb 0xdfac189f85c07cf0

def z512 : W := mkw 0xa75cf5288cd59ab3 0xdd38f8b6ef86ddbd 0xfff9f07f8fc7f8ff 0xdfacd89fe5c67cfc

def z513 : W := mkw 0xe4ca52bc964ec9d9 0xcd02165c91b57afa 0xe3c7ffffffffffff 0xffd33f789fffffff

def z514 : W := mkw 0xa75cd4288cd49ab1 0xcd08f816e986d8bd 0xfffff07f8ffff8ff 0xffecf89ffdc7fcff

def z515 : W := mkw 0x60420294120a4149 0xcd001410803162d2 0xe3c00ffc7e3fc7fb 0xdfc018188239f3f3

def z516 : W := mkw 0xa548502884448893 0xcd3f98ffc18458b8 0xfff9f07f8fc7f8ff 0xdfbfd8ffe5c67cfc

def z517 : W := mkw 0xa75c712884d59ab1 0xcd0898b6e9845dbd 0xfffff07f8fc7ffff 0xffecd8fffdc67fff

def z518 : W := mkw 0x0200000000000000 0x0000600028000000 0x03fe000000000000 0xa000e000f8000000

def z519 : W := mkw 0x60c3cef65f2a414b 0xdf3fff5896fff2d2 0xe001fffffffe00c3 0x9ebfff1807fff0e0

def z520 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfff9ffffffc1ffff 0xddbfc0ffe7fe0ffc

def z521 : W := mkw 0xe0c2129c120ac149 0xcd02165c91316af2 0xffc7fffffe3ffffb 0xffff3fff9ff9fff3

def z522 : W := mkw 0x0001084000000000 0x1000000006480000 0x0001fffff0000000 0x1800000007f80000

def z523 : W := mkw 0x0001084000000002 0x1035000006480000 0x0001f00380000000 0x002c000005c00000

def z524 : W := mkw 0x0001084000000002 0x1035000006480000 0x00000f8070000000 0x0013000002380000

def z525 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c600000e3fc7f8 0xe7c03f789801f3f3

def z526 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe0000ffc7e3fc7f9 0x1fc31f180239f3f3

def z527 : W := mkw 0x60c286941a0a414b 0xdd3276589633e2d2 0xe3c7fffc7fffc7fb 0xfff3ff789e3ff3f3

def z528 : W := mkw 0x4801afd76b216402 0x12b765e9067ba740 0x00000f8070380700 0x0013276002398300

def z529 : W := mkw 0x0000210000010002 0x103000a006000500 0x0001f00000003800 0x0020008004000c00

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z531 : W := mkw 0x0000000000000002 0x0035610000000000 0x0000000000000000 0x0013270000000000

def z532 : W := mkw 0x60c20294120a4148 0x0d020648103162d2 0x00060ffc7e3fc7f8 0x3fd327601a39f3f3

def z533 : W := mkw 0x0215af524bb11222 0x123565a02e5ba505 0x00060f8070380700 0x205327601a398303

def z534 : W := mkw 0x11a14a7247200001 0xe20f9f5bd0dd3000 0xfc00007ff0060001 0x0a0f1f1f01f87000

def z535 : W := mkw 0x8001de7a4f208002 0x123ded0407dfb820 0xfc01fffffffff8c3 0xdfbfff9f07fffce0

def z536 : W := mkw 0x0100000000000001 0xc0001012c0000000 0xfff8000000000000 0x4000009fe0000000

def z537 : W := mkw 0xa549dc6acd648893 0xdf3df916c7ced8b8 0xfff9f07f8fc7f8ff 0xdfacd89fe5c67cfc

def z538 : W := mkw 0xa549de7acf648893 0xdf3dfd16c7dff8b8 0xfc01fffffffe00c3 0x9ebfff1f07fff0e0

def z539 : W := mkw 0x40820294120a4148 0x0002064810312242 0x03c60f807e39c73a 0xf55327609a398313

def z540 : W := mkw 0xed4939cda045ec93 0xddb710ffc7684ff8 0xfff9fffff001ffff 0x59bf00ffe7f80ffc

def z541 : W := mkw 0xa75c310880d59ab1 0xcd0010b6e9004dbd 0xfffe00000001fffc 0x61c000fff8000fff

def z542 : W := mkw 0x8000100800008000 0x0000000401000820 0x0001f07f8001f8c0 0x1980000005c00ce0

def z543 : W := mkw 0x0214a50008911222 0x103de9a02e028505 0x03ffff800ff9ff3f 0xf57fffe0fe078f1f

def z544 : W := mkw 0x1334a50008911222 0x303de9a36e028505 0x1c39f00001c03804 0x002cc08764060c0c

def z545 : W := mkw 0x97a8502884448893 0xe03ffbfff9841828 0xfffff00381c03807 0xe03ffffffdc60c0c

def z546 : W := mkw 0xa5ca5238964e89d9 0xcd089e16d19578ba 0xfffff07f8ffff8ff 0xffecff9ffdc7fcff

def z547 : W := mkw 0x8001184800008002 0x1035000407480820 0xfc01fffff001f8c3 0x59bf009f07f80ce0

def z548 : W := mkw 0x60d6a7941a9b5369 0xdd0216589633e7d7 0xe3c7fffc7fffffff 0xffd33f789e3fffff

def z549 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc06000000000001 0x201f3f7f18000000

def z550 : W := mkw 0x0314a50008911223 0xd038f8b2ee028505 0xffffff800ff9ff3f 0xf57cf8fffe078f1f

def z551 : W := mkw 0x0214840008901220 0x0000600028028005 0x03fe0f800ff9c73e 0xf550e060fa07831f

def z552 : W := mkw 0x2448402084440890 0x0d00000000845098 0x000000000fc6003c 0x060000000006701c

def z553 : W := mkw 0x0000402004000000 0x0008880000841000 0x000000000fc60000 0x8600d80000067000

def z554 : W := mkw 0x4000218400014002 0x103200e806200740 0xe001fffc7001ffc3 0x59b300f806380fe0

def z555 : W := mkw 0x0294a50008911223 0xd03272f8be028505 0xe3ffff800ff9ff3f 0xf573fff8fe078f1f

def z556 : W := mkw 0xc8833bdd320be54a 0x10b706ed17792f62 0xfc07fffff039ffc3 0x79ff27ff1ff98fe3

def z557 : W := mkw 0xc80139cd2001e400 0x108200ed07680f60 0xfc01fffff001ffc0 0x598000ff07f80fe0

def z558 : W := mkw 0x13a0c6324f200001 0xe208ff12f897b000 0x03fe00000ffe0000 0xa600ff00f807f000

def z559 : W := mkw 0x4083cef65f2a414a 0x123fef4816ffb242 0x0007fffffffe0703 0xbe7fff601ffff303

def z560 : W := mkw 0xdb2139cd2001e402 0x30bfe9ef6f680f60 0xfc39fffff001ffc3 0x59bfc0ff67f80fe0

def z561 : W := mkw 0x0101ce724f200003 0xd23dfd12c6dfb000 0xfff9fffffffe0003 0xde3fff9fe7fff000

def z562 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0x03fe000000000000 0xa013ff60f8000000

def z563 : W := mkw 0x13b5ef724fb11223 0xf23ffffbfedfb505 0xffffffffffffff3f 0xff7fffffffffff1f

def z564 : W := mkw 0x40838ed65b2a414a 0x12376748167ba242 0x00060f8070380700 0x205327601a398303

def z565 : W := mkw 0x62c20294120a414b 0xcd3276f8b83162d2 0xe3fe0ffc7e3fc7fb 0xfff3fff8fa39f3f3

def z566 : W := mkw 0x13a0210000010003 0xf03ffbfbfe000500 0xffffff800001ff03 0xf13ffffffe000f00

def z567 : W := mkw 0x22d6a7101a9b136b 0xdd3076b0be13e597 0x03ffff800fffff3e 0xf770ffe0fe07ff1f

def z568 : W := mkw 0xc801fdef6d21e402 0x12bfe9ed07ee9f60 0xfc01fffff1c1ffc3 0x59bfc0ff07fe0fe0

def z569 : W := mkw 0x0014a50008911220 0x1000000006028505 0x03c7ff800ff9ff3e 0xf55020609e078f1f

def z570 : W := mkw 0x20c20210120a0149 0xcd02165890116092 0xe3c600000e3e003b 0xe6533f789801f013

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x03f8000000000002 0xc020c080e0000000

def z572 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3fffffc7fffffff 0xfff3fff8fe3fffff

def z573 : W := mkw 0x0014a50008911222 0x1030600006028505 0x0001ff800ff9ff3e 0x9570e00006078f1f

def z574 : W := mkw 0xc80179ed2401e402 0x10bf88ed07ec1f60 0xfc01ffffffc7ffc3 0xdfbfd8ff07fe7fe0

def z575 : W := mkw 0x20c0000000000001 0xcd02125890004090 0xe3c6007c0e07c0fb 0xff933f78980070f0

def z576 : W := mkw 0xa548712884458893 0xdd3898b6c7845db8 0xfff9ffff8fc7ffff 0xdfbcd8ffe7c67ffc

def z577 : W := mkw 0xc80139cd2001e402 0x10b000a407680f60 0x0001fffff001ffc2 0x59b000e007f80fe0

def z578 : W := mkw 0x0000021002000002 0x003ded0000112000 0x00000ffc7e3e0003 0x9e3fff000239f000

def z579 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0007ff800ff9ff3c 0x355020601e078f1f

def z580 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03c60f800e39c73a 0xf55020609a018313

def z581 : W := mkw 0x8508100880448890 0x0000000641000828 0x1c38000000003804 0x0000008760000c0c

def z582 : W := mkw 0x0100000000000001 0xc0089812c0000000 0x03f8000000000000 0x8000d800e0000000

def z583 : W := mkw 0x0014a50008911220 0x1000000006028505 0x03f9ff800ff9ff3e 0xd560c080e6078f1f

def z584 : W := mkw 0x1321cc624d200002 0x323de9a36ece9000 0x1c39f00381c00000 0x002cc08765c60000

def z585 : W := mkw 0x275cc4208cd41ab1 0xcd08f812e886d09d 0x03fe00000ffe003c 0xa640f800f807f01f

def z586 : W := mkw 0x0000a50008010002 0x103060a006028500 0x0001ff800ff9ff02 0xd530e0e006078f00

def z587 : W := mkw 0x0214a50008911220 0x100000a02e028505 0x03ffff800ff9ff3c 0x754000e0fe078f1f

def z588 : W := mkw 0xa548100880448891 0xcd001016c10048b8 0xfff9f07f8001f8ff 0x59ac009fe5c00cfc

def z589 : W := mkw 0x0000210000010002 0x103700e906000500 0xfc01ff800001ff03 0x513f00ff06000f00

def z590 : W := mkw 0xc80139cd2001e400 0x1082004c07680f60 0xe001fffff001ffc3 0x5993007807f80fe0

def z591 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fe0f800039ff3c 0x615020e0fa018f1f

def z592 : W := mkw 0x33e20210120a014b 0xed3ffffbf8116092 0xfffe00000e3e003b 0xe67ffffff801f013

def z593 : W := mkw 0xa448502884448890 0x0d088804018458b8 0x0001f07f8fc7f8ff 0x9facd80005c67cfc

def z594 : W := mkw 0x880139492001a400 0x1080000407480d20 0x0001f00380003800 0x0000000005c00c00

def z595 : W := mkw 0x0214a50008911222 0x103760e92e028505 0xffffff800ff9ff3f 0xf57fe0fffe078f1f

def z596 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x003fff8001f83f04 0x2070e0e07e078f0f

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0x03f800000001f83c 0x41000080e0000c1c

def z598 : W := mkw 0x48832bd5320b654a 0x10b706e916792742 0x00060f8070380700 0x205327601a398303

def z599 : W := mkw 0x0215af524bb11222 0x123565a02e5ba505 0x03ffff807ff9ff3e 0xf573e7e0fe3f8f1f

def z600 : W := mkw 0x0000402004000000 0x0008880000841000 0x0000007f80060001 0x0a0c180001c07000

def z601 : W := mkw 0xa55cf5288cd59ab1 0xdd089816c786ddbd 0xfff9ffff8fffffff 0xdfecd89fe7c7ffff

def z602 : W := mkw 0x20c20210120a0149 0xcd00161090116092 0xe3c6007c0e3fc0fb 0xffc03f189801f0f3

def z603 : W := mkw 0xb7e8502884448891 0xed0a9afff98458b8 0xfffff07f8fc7f8ff 0xffacd8fffdc67cfc

def z604 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0x03c60f807e3e0738 0xa6533f609a39f313

def z605 : W := mkw 0x40820084100a4148 0x0002024810200242 0x0006000000000700 0x2040006018000303

def z606 : W := mkw 0x13b4840008901221 0xe008fb12f8028005 0x03fe00000ff8003c 0xa440ff00f807801f

def z607 : W := mkw 0x8100100800008001 0xc0089816c1000820 0xfff9f07f8001f8c3 0xd9acd89fe5c00ce0

def z608 : W := mkw 0xcd0979eda445ec92 0x10bf88ef47ec1f68 0xfc39fffff1c1ffc7 0x59bfc0ff67fe0fec

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000007c0e060003 0x9e00180000007000

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001f0000fc00002 0x9420c00004060000

def z611 : W := mkw 0xe5ca52bc964ec9d9 0xcd0a9e5ed1b57afa 0xfff9f07fffc7f8ff 0xdfafdf9fe5fe7cfc

def z612 : W := mkw 0x6256a7941a9b536a 0x1d3064a02e33e7d7 0x03fffffc7ffffffe 0xfff0e0e0fe3fffff

def z613 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0x1c01ff83f0003f00 0x003f00e707f80f00

def z614 : W := mkw 0x8801fd6b6d21a402 0x12bde9a507ce9d20 0x1c01f00381c03800 0x002cc08705c60c00

def z615 : W := mkw 0x8509de7acf648892 0x123ded0647dfb828 0x1c39fffffffe3807 0x9e3fff8767fffc0c

def z616 : W := mkw 0x0000c6324f200000 0x020004000097b000 0x000000000ffe0000 0x060000000007f000

def z617 : W := mkw 0xfbe33bdd320be54b 0xfdbfffffff796ff2 0xfffffffffe3ffffb 0xfffffffffff9fff3

def z618 : W := mkw 0x0001cc624d200002 0x123de90006ce9000 0x0001fffff1c00003 0x183fc00007fe0000

def z619 : W := mkw 0xdba1ffff6f21e403 0xf2bfffffffffbf60 0xffffffffffffffc3 0xffbfffffffffffe0

def z620 : W := mkw 0x4000008400004002 0x003700e900200240 0xfc000ffc7001c7c3 0x59bf00ff023803e0

def z621 : W := mkw 0x2548402084440891 0xcd089812c0845098 0xfff800000fc6003f 0xc62cd89fe006701c

def z622 : W := mkw 0x13a0000000000001 0xe00212fbf8000000 0xfffe000000000003 0xe0133ffff8000000

def z623 : W := mkw 0x480129c520016402 0x10b700e906680740 0xfc000f8070000703 0x403f00ff02380300

def z624 : W := mkw 0xc8013bdd2201e402 0x10b704ed07792f60 0xfc01fffffe3fffc3 0xdfbf3fff07f9ffe0

def z625 : W := mkw 0xe8c3ffff7f2be54b 0xdfbffffd97fffff2 0xffc7fffffffffffb 0xffffffff9ffffff3

def z626 : W := mkw 0xe5ca50ac944ec9d9 0xcd0a9a5ed1a45afa 0xfffff07f8fc7ffff 0xffecd8fffdc67fff

def z627 : W := mkw 0x1320000000000002 0x203fe9eb68000000 0xfc38000000000003 0x403fc0ff60000000

def z628 : W := mkw 0x13a0000000000001 0xe00afb5af8000000 0xe3fe000000000003 0xe013ff78f8000000

def z629 : W := mkw 0x0214210000911220 0x000000a028000505 0x0038000000003804 0x0000008060000c0c

def z630 : W := mkw 0x0000000000000002 0x003de90000000000 0x0000000000000000 0x002cc00000000000

def z631 : W := mkw 0xb7e9de7acf648893 0xff3fffffffdff8b8 0xfffffffffffff8ff 0xffbffffffffffcfc

def z632 : W := mkw 0x0001ce724f200002 0x1235040006dfb000 0x0001fffffffe0003 0x1e3f000007fff000

def z633 : W := mkw 0x0214000000901220 0x0000000028000005 0x03fe00000000003c 0x20400000f800001f

def z634 : W := mkw 0x0000000000000002 0x0035000000000000 0x0000000000000003 0x003f000000000000

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000ffc70000003 0x1813000002380000

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001f07f80000003 0x182c000005c00000

def z637 : W := mkw 0x9b2139492001a402 0x30bde9a76f480d20 0x1c39f00380003800 0x002cc08765c00c00

def z638 : W := mkw 0x0215ed624db11222 0x123de9a02ece9505 0x03ffff838ff9ff3e 0xf57ce0e0ffc78f1f

def z639 : W := mkw 0x4214a58408915222 0x103260e82e228745 0xe3fffffc7ff9ffff 0xfdf3e0f8fe3f8fff

def z640 : W := mkw 0x60c34af6572a4149 0xcf0f9f5890fd72d2 0xe000007ff00600c1 0x0a8f1f1801f870e0

def z641 : W := mkw 0x60c20294120a414b 0xcd3716f9903162d2 0xffc60ffc7e3fc7fb 0xffff3fff9a39f3f3

def z642 : W := mkw 0x20c2c6325f2a0149 0xcf08ff109097f092 0x03c600000ffe0038 0xa640ff009807f013

def z643 : W := mkw 0x4296a7941a9b536a 0x103266e83e33a747 0x00060f8070380700 0x205327601a398303

def z644 : W := mkw 0x60c22394120b414b 0xdd3216f8963167d2 0xe3c7fffc7e3ffffb 0xfff33ff89e39fff3

def z645 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe0000ffc7007c7c3 0x5b931f78023873e0

def z646 : W := mkw 0x4801eff76f216402 0x12bfede906ffb740 0x0001fffffffe0703 0x9e3fff6007fff300

def z647 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c6007c7e3e00f9 0xaec33f189839f0f3

def z648 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fff00001c1ff3c 0x6160c0e0fc060f1f

def z649 : W := mkw 0x880139492001a402 0x10b500a507480d20 0xfc01f07f8001f8c3 0x59ac009f05c00ce0

def z650 : W := mkw 0xed4958eda444ec91 0xcd8f985fc1ec5af8 0xfc00007ff00600c1 0x0a8f181f01f870e0

def z651 : W := mkw 0x4000029402004000 0x0002044800312240 0xe0000ffc7e3fc7c3 0xdf933f780239f3e0

def z652 : W := mkw 0x2040000000000001 0xcd00101080004090 0xe3c60ffc0e3fc7fb 0xffd038789a01f3f3

def z653 : W := mkw 0x0000000000000000 0x000200e900000000 0xfc00000000000000 0x400000ff00000000

def z654 : W := mkw 0x2140000000000001 0xcd089812c0004090 0xfff8007c0e07c0fb 0xdfacd89fe00070f0

def z655 : W := mkw 0x0001ce724f200002 0x1235650006dfb000 0x0001fffffffe0000 0x1e13270007fff000

def z656 : W := mkw 0x2040000000000001 0xcd00101080004090 0x03c000000e060038 0x8600180080007010

def z657 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x0039ff8001c1ff06 0x5130c0e066060f0c

def z658 : W := mkw 0x0001cc624d200002 0x123de90006ce9000 0x0001f00381c00003 0x803fff0005c60000

def z659 : W := mkw 0x2254a50008911223 0xdd3070b0ae02c595 0xe3fffffc0fffffff 0xfff0f8f8fe07ffff

def z660 : W := mkw 0x8a15bd492891b622 0x10b560a52f4a8d25 0x1fffff838ff9ff3e 0xf57ce0e7ffc78f1f

def z661 : W := mkw 0x65ca42b4964e49d9 0xcd0a9e5ad0b572da 0xe3fe0ffc7fffc7ff 0xffd3ff78fa3ff3ff

def z662 : W := mkw 0xc8015aff6720e400 0x028f8d4d01fd3a60 0xfc00007ff00600c1 0x0a8f1f1f01f870e0

def z663 : W := mkw 0x0080000000000001 0xc000121090000000 0x03c6000000000000 0xa0003f0098000000

def z664 : W := mkw 0x1320000000000000 0x2008e90268000000 0x0038000000000000 0x0000c00060000000

def z665 : W := mkw 0x13a1ce724f200003 0xf23dff12fedfb000 0x03fffffffffe0003 0xbe3fff00fffff000

def z666 : W := mkw 0xe5ca129c924ec9d9 0xcd02165ed1316afa 0xfffe0ffc7e3fffff 0xffd33ffffa39ffff

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc00000000000003 0x402c009f00000000

def z668 : W := mkw 0x0080000000000000 0x0002024810000000 0x0006000000000000 0x2013276018000000

def z669 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fff00001c03806 0xe030e0e0fc060c0c

def z670 : W := mkw 0xb7e8502884448891 0xed08fb16f98458b8 0xfffff07f8fc7f8ff 0xffacff9ffdc67cfc

def z671 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc01f07f8007f8c3 0x5bac189f05c07ce0

def z672 : W := mkw 0x0100402004000001 0xc0089812c0841000 0xfff9f07f8fc60003 0xde2cd89fe5c67000

def z673 : W := mkw 0x0200000000000002 0x003060a028000000 0x0006000000000000 0x2010206018000000

def z674 : W := mkw 0x0001084000000002 0x103700e906480000 0xfc01fffff0000003 0x583f00ff07f80000

def z675 : W := mkw 0xe8433bdd320be54a 0x1db704ed07796ff2 0xfc01fffffe3ffffb 0x5fff00ff07f9fff3

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000003 0x80133f0000000000

def z677 : W := mkw 0x13a0021002000003 0xe03ffffbf8112000 0xfffe0ffc7e3e0003 0xfe3ffffffa39f000

def z678 : W := mkw 0x0014a50008911220 0x1000000006028505 0x00000f8000380700 0x0040000002018303

def z679 : W := mkw 0x62d62184109b5369 0xcd0212f8b82047d7 0xe3fe00000001fffc 0x61c000f8f8000fff

def z680 : W := mkw 0x2548000080440891 0xcd001012c0004098 0x03f800000000003c 0x00000000e000001c

def z681 : W := mkw 0x0200000000000000 0x000000a028000000 0x03fe000000000000 0x600000e0f8000000

def z682 : W := mkw 0x62d6a584189b536b 0xdd3272f8be22c7d7 0xe3ffff800ff9fffe 0xf5f0e0f8fe078fff

def z683 : W := mkw 0x20c20210120a0149 0xcd00161090116092 0x03c60ffc7e3e003b 0xbe533f009a39f013

def z684 : W := mkw 0x60420294120a4148 0x0d000400003162d2 0x00000ffc7e3fc7fb 0x9fd33f000239f3f3

def z685 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff8007f8fc600fd 0x8e8cd81fe1c670fc

def z686 : W := mkw 0x00820210120a0148 0x0000060010112002 0x0006000000380000 0x2040270018018003

def z687 : W := mkw 0x0000210000010002 0x103000a006000500 0x03c7ff800e39ff3a 0xf57020e09e018f13

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c600000e380038 0xa440200098018013

def z689 : W := mkw 0x12a0000000000002 0x203763e938000000 0x03fe000000000002 0xe033e7e0f8000000

def z690 : W := mkw 0x60c3cef65f2a4149 0xdf02165896fff2d2 0xe3c7ffffffffc7fb 0xffd33f789ffff3f3

def z691 : W := mkw 0x4800218520016400 0x008200e900200740 0x0000000000000700 0x0000006000000300

def z692 : W := mkw 0xa5495a7ac7648891 0xcf0d9d16c1dd78b8 0xfc00007ff00600c1 0x0a8f1f1f01f870e0

def z693 : W := mkw 0x8408502884448890 0x0000000401841828 0x0001f00381c03804 0x0000000005c60c0c

def z694 : W := mkw 0x0001486004000002 0x103d880006cc1000 0x0001ffffffc60003 0x9e3fd80007fe7000

def z695 : W := mkw 0xa448100880448890 0x0d000004010048b8 0x000000000001f8fc 0x0180000000000cfc

def z696 : W := mkw 0xb7e8502884448893 0xed3ffbfff98458b8 0xfffe007f800600c3 0xeabffffff9c070e0

def z697 : W := mkw 0x73e20084100a4149 0xed0212fbf82042d2 0xfffe00000001c7f8 0x61c000fff80003f3

def z698 : W := mkw 0x5aa129c520016402 0x30b763e93e680740 0x00060f8070000700 0x201327601a380300

def z699 : W := mkw 0xffe979eda445ec93 0xfdbffbffffec5ff8 0xffffffffffc7ffff 0xffbffffffffe7ffc

def z700 : W := mkw 0xa548502884448893 0xcd3df916c18458b8 0xfff9f07f8fc7f8ff 0xdfbfff9fe5c67cfc

def z701 : W := mkw 0xe54850ac8444c891 0xcd0a985ec1a45af8 0xfff9ffffffc7ffff 0xdfbfd8ffe7fe7ffc

def z702 : W := mkw 0x0000210000010000 0x000000a000000500 0x000000000001ff00 0x410000e000000f00

def z703 : W := mkw 0x0214a7100a911222 0x103064a02e13a505 0x03fffffc7fffff3f 0xff73ffe0fe3fff1f

def z704 : W := mkw 0x0000402004000002 0x003de90000841000 0x0001f07f8fc60003 0x9e3fff0005c67000

def z705 : W := mkw 0x0200000000000002 0x003060a028000000 0x03fff0000fc1f83e 0xf530e0e0fc060c1c

def z706 : W := mkw 0x0000402004000000 0x0008880000841000 0x0001f00381c00000 0x002cc00005c60000

def z707 : W := mkw 0x0000840008000002 0x1030600006028000 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z708 : W := mkw 0xc801ffff6f21e402 0x12b064a407ffbf60 0x0001ffffffffffc2 0xdfb0e0e007ffffe0

def z709 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0000007ff0060003 0x8a1f3f0001f87000

def z710 : W := mkw 0x13a0000000000001 0xe00ffbfbf8000000 0xfffe000000000001 0xe00ffffff8000000

def z711 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff001ffc0 0x59ac00ff07f80fe0

def z712 : W := mkw 0x13a0000000000003 0xe03dfbb3f8000000 0x1c38000000000000 0x002cdf8760000000

def z713 : W := mkw 0xc80139cd2001e400 0x008700ed01680f60 0xfc01f07ff001ffc3 0x59af00ff05f80fe0

def z714 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc39f07f8fc638c7 0x9eacd89f65c67cec

def z715 : W := mkw 0x0214a50008911222 0x103560a02e028505 0x03ffff800ff9ff3f 0xf57fe0e0fe078f1f

def z716 : W := mkw 0xa75cf5288cd59ab3 0xdd38f8b6ef86ddbd 0xfc060fff803e07c1 0x2adc387f1bc1f3e3

def z717 : W := mkw 0x00010a5002000002 0x103ded0006592000 0x0001fffffe3e0003 0x9e3fff0007f9f000

def z718 : W := mkw 0x0201ef724f210002 0x123deda02edfb500 0x03ffffffffffff03 0xff3fffe0ffffff00

def z719 : W := mkw 0x12a0000000000003 0xe03773f9b8000000 0xffc6000000000003 0xe03f3fff98000000

def z720 : W := mkw 0xea57bfdd3a9bf76a 0x1db064a42f7beff7 0x03fffffffffffffe 0xfff0e0e0ffffffff

def z721 : W := mkw 0x71e20084100a4149 0xed0f9b5bd02042d2 0xfc000000000000c1 0x008f1f1f000000e0

def z722 : W := mkw 0x0180000000000003 0xc03f9afbd0000000 0xfffe000000000003 0xe03ffffff8000000

def z723 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfc06000000000001 0x201f3f7f18000000

def z724 : W := mkw 0x53a0218400014003 0xf03ffbfbfe200740 0xfffffffc7001ffc3 0xf9bffffffe380fe0

def z725 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfc00000000000003 0x401f1f7f00000000

def z726 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc01f07ff00000c3 0x18af001f05f800e0

def z727 : W := mkw 0x13a18c4008000003 0xf03ffbfbfe4a8000 0xfffffffffff80003 0xfc3fffffffff8000

def z728 : W := mkw 0x1320000000000002 0x203fe9eb68000000 0xfc38000000000003 0xc03fffff60000000

def z729 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe0060ffc703fc7c3 0x7bd33f781a39f3e3

def z730 : W := mkw 0x0201ce724f200002 0x123ded002edfb000 0x03fffffffffe0003 0xbe3fff00fffff000

def z731 : W := mkw 0x35e8402084440891 0xed0f9b5bd0845098 0xfff800000fc6003d 0x860fdf1fe006701c

def z732 : W := mkw 0x00018e524b200002 0x12356500065ba000 0x0001fffffe3e0003 0x9e3f3f0007f9f000

def z733 : W := mkw 0x0001ce724f200002 0x123704e906dfb000 0xfc01fffffffe0003 0x5e3f00ff07fff000

def z734 : W := mkw 0xe8433bdd320be548 0x1d80040407796ff2 0x0001fffff007ffc0 0x1b80000007f87fe0

def z735 : W := mkw 0x8001184800008002 0x1035000407480820 0xfc01fffff00000c3 0x18bf001f07f800e0

def z736 : W := mkw 0x0201ce724f200002 0x123deda02edfb000 0x03fffffffffff83f 0xff3fffe0fffffc1c

def z737 : W := mkw 0xe44a129c924ec9d8 0x0d00040401316afa 0x00000ffc7e3ffffc 0x1fc000000239ffff

def z738 : W := mkw 0x0214a50008911222 0x103fe9e92e028505 0xffffff800ff9ff3f 0xf57ffffffe078f1f

def z739 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0001fffffffe0003 0x9e3fff0007fff000

def z740 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03ffffffffffff3f 0xff7fffe0ffffff1f

def z741 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc060ffff03807c1 0x28df207f1bf983e3

def z742 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0x1ffe000000000000 0xa03fffe7f8000000

def z743 : W := mkw 0x02156b7247b11220 0x020d8da028dd3505 0x03fe007ff007ff3d 0x6b4f1fe0f9f87f1f

def z744 : W := mkw 0x0015ef724fb11222 0x123ded0006dfb505 0x03f9ffffffffff3f 0xdf7fff80e7ffff1f

def z745 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xffc6000000000001 0xa00f3f1f98000000

def z746 : W := mkw 0x0001ce724f200002 0x123d8d0006dfb000 0x0001fffffffe0003 0x1e3f1f0007fff000

def z747 : W := mkw 0x13a0000000000002 0x203febeb78000000 0x1c38000000000000 0x002fc78760000000

def z748 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfff9fffff001ffff 0x59bf00ffe7f80ffc

def z749 : W := mkw 0x13b5ed624db11223 0xf23ffbfbfece9505 0xffffff838ff9ff3f 0xf57fffffffc78f1f

def z750 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03ffff800ff9ff3c 0xb550e060fe078f1f

def z751 : W := mkw 0xc58a52bc964ec9d8 0x000a8e4e51b53a6a 0x1c3fff83f1f83f04 0x207fe7e77fff8f0f

def z752 : W := mkw 0x0100000000000001 0xc0089812c0000000 0xfff8000000000003 0xc03fff9fe0000000

def z753 : W := mkw 0x73620294120a414a 0x2d3deda3683162d2 0x1c380ffc7e3fc7f8 0x1fecc0876239f3f3

def z754 : W := mkw 0x33e0000000000003 0xed3ffbfbf8004090 0xfffe00000001c0fb 0xe1bffffff80000f0

def z755 : W := mkw 0x0215ce724fb01222 0x123ded002edfb005 0x0039fffffffe0007 0x9e3fff0067fff00c

def z756 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01f07ff001f8c3 0x59af009f05f80ce0

def z757 : W := mkw 0x53a0008400004003 0xe03ffbfbf8200240 0xfffe00000001c7c3 0xe1bffffff80003e0

def z758 : W := mkw 0x0100000000000001 0xc008f912c0000000 0xfff8000000000003 0xc02cff9fe0000000

def z759 : W := mkw 0x37e8402084440893 0xed3ffbfbf8845098 0xfffe007c0fc7c0ff 0xffbffffff80670fc

def z760 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03c1ffffffffc03b 0xdf3fff0087fff010

def z761 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc3e000000000001 0x203fffff78000000

def z762 : W := mkw 0x11b4a50008911221 0xf00f9b5bd6028505 0xfc01ff800ff9ff3d 0x154f1f1f06078f1f

def z763 : W := mkw 0x5bb5adc528917623 0xf0bffbfbfe6a8745 0xffffff807ff9ff3f 0xf57ffffffe3f8f1f

def z764 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc38000000000003 0x403fdfff60000000

def z765 : W := mkw 0x0001ce724f200000 0x12088c0006dfb000 0x0001fffffffe0003 0x9e3fff0007fff000

def z766 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x00000ffffe3e0001 0x1e0f1f0003f9f000

def z767 : W := mkw 0x00014a7247200002 0x023d8d0000dd3000 0x0000007ff0060003 0x0a3f1f0001f87000

def z768 : W := mkw 0x33e0402004000003 0xed3ffbfbf8845090 0xfffff07f8fc7c0fb 0xffbffffffdc670f0

def z769 : W := mkw 0x4a97afd53a9b776a 0x10b766e93e7ba747 0x00060f8070380700 0x205327601a398303

def z770 : W := mkw 0x13b4a50008911223 0xf03afbfbfe028505 0xffffff800ff9ff3e 0xf570fffffe078f1f

def z771 : W := mkw 0x27dec6309ede1bf9 0xcd08fe12f897f09f 0x03fe00000ffe003c 0xa640ff00f807f01f

def z772 : W := mkw 0x13a0840008000003 0xf03ffbfbfe028000 0xfffe0f8000380003 0xe03ffffffa018000

def z773 : W := mkw 0x13a1ce724f200001 0xf20216fbfedfb000 0xfffffffffffe0000 0x7e0000fffffff000

def z774 : W := mkw 0x71e20084100a4149 0xed0f9b5bd02042d2 0xffc600000001c7f9 0x61cf1f7f980003f3

def z775 : W := mkw 0x40820294120a4148 0x0002064810312242 0xe0060ffc7e3fc7c3 0xffd33f781a39f3e3

def z776 : W := mkw 0xc8013bdd2201e400 0x1080040407792f60 0x0001fffffe3fffc0 0x1f80000007f9ffe0

def z777 : W := mkw 0x13b5ad4008911223 0xf03ffbfbfe4a8505 0xfffffffffff9ff3f 0xfd7fffffffff8f1f

def z778 : W := mkw 0x13a0000000000001 0xe00713fbf8000000 0xfffe000000000000 0x600307fff8000000

def z779 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfffffffff039ffff 0x79ff20fffff98fff

def z780 : W := mkw 0x0001ef724f210002 0x123deda006dfb500 0x0001fffffffe0703 0x9e3fff6007fff300

def z781 : W := mkw 0xc80118cd2000e402 0x10b7004d07680a60 0xfc000ffff00000c1 0x089f001f03f800e0

def z782 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000001 0xa02fff9ff8000000

def z783 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfffffffff1c1ffff 0x79ffc0fffffe0fff

def z784 : W := mkw 0x73f6a584189b536b 0xfd3ffbfbfe22c7d7 0xffffff800ff9ffff 0xf5fffffffe078fff

def z785 : W := mkw 0xdab5bdcd2891f622 0x30b763ed3f6a8f65 0xfc07fffff039ffc3 0x79ff27ff1ff98fe3

def z786 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001ffffffffc73b 0x9f7fff0007fff313

def z787 : W := mkw 0x11a0000000000001 0xe0089b12d0000000 0xfc00000000000001 0x000c1f1f00000000

def z788 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfff8000000000003 0xc02fdf9fe0000000

def z789 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0000007fffc60001 0x8e0fdf0001fe7000

def z790 : W := mkw 0x2548c632cf640891 0xcf08fd12c097f098 0x000000000ffe0000 0x8600ff000007f000

def z791 : W := mkw 0xc801deff6f20e400 0x1280040407ffba60 0x0001fffffffe00c0 0x1e80000007fff0e0

def z792 : W := mkw 0xa5499e5acb648893 0xdf357516c75be8b8 0xfff80f807039f8fc 0x4193279fe2398cfc

def z793 : W := mkw 0xa4c8502884448891 0xcd02125c918458b8 0xe3c7f07f8fc7f8ff 0xff933f789dc67cfc

def z794 : W := mkw 0x13b4210000911223 0xe03ffbfbf8000505 0xfffe0f800e39ff3f 0xf57ffffffa018f1f

def z795 : W := mkw 0xc80139cd2001e402 0x00b700ed01680f60 0xfc00007ff001ffc3 0x49bf00ff01f80fe0

def z796 : W := mkw 0xc80139cd2001e402 0x10b000a407680f60 0xfc01fffff001ffc3 0x59bc00ff07f80fe0

def z797 : W := mkw 0x13a0000000000002 0x203febeb78000000 0x1ffe000000000002 0xe03fe7e7f8000000

def z798 : W := mkw 0x60c3cce65d2a414b 0xdf3ffb5896eed2d2 0xe3c7f00381c1c7f8 0x61ecc0789dc603f3

def z799 : W := mkw 0x13b4a50008911222 0x303febeb7e028505 0x1fffff800ff9ff3e 0xf57fe7e7fe078f1f

def z800 : W := mkw 0xc214b58c0891d222 0x103260ec2f228f65 0xfffffffffff9ffff 0xfdffe0ffffff8fff

def z801 : W := mkw 0x11a0000000000003 0xe03f9b5bd0000000 0xfc00000000000003 0x003f1f1f00000000

def z802 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03c7fffffffe0003 0xfe3fff609ffff000

def z803 : W := mkw 0x8001394800018002 0x103500a407480d20 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z804 : W := mkw 0x0a15ad4128913622 0x10b560a12e4a8505 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z805 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffffffff803 0xdf3fff8007fffc00

def z806 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000000 0xe02cfffff8000000

def z807 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fffffc7ff9ff3f 0xfd73e0e0fe3f8f1f

def z808 : W := mkw 0x5ba129c520016403 0xf0bffbfbfe680740 0xffffff807001ff03 0xf13ffffffe380f00

def z809 : W := mkw 0x00014a7247200000 0x0200040000dd3000 0x00000ffffe3e0003 0x9e133f0003f9f000

def z810 : W := mkw 0x62d6a7941a9b536b 0xdd3276f8be33e7d7 0xe039f07c71c638c5 0x0aa3df98643e7cec

def z811 : W := mkw 0x37e8c632cf640891 0xef08ff12f897f098 0x03fe00000ffe003c 0xa600ff00f807f01c

def z812 : W := mkw 0x13a1084000000003 0xf03ffbfbfe480000 0xfffe0f8070000003 0xe03ffffffa380000

def z813 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x00000ffff03e0003 0x8a3fff0003f9f000

def z814 : W := mkw 0x00014a7247200002 0x023ded0000dd3000 0x0001f07fffc60003 0x9e3fff0005fe7000

def z815 : W := mkw 0x31e0000000000001 0xed0f9b5bd0004090 0xffc0007c0e07c0fb 0xdf8f1f1f800070f0

def z816 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe00000fc0003f 0xe43ffffff806001c

def z817 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfff9ffffffc1ffff 0xddbfc0ffe7fe0ffc

def z818 : W := mkw 0x6d4969e5a4456c93 0xddbf98fbc6ec57d8 0x03f80f807fc6073c 0x8613d860e23e731c

def z819 : W := mkw 0xc80118cd2000e400 0x0080000401680a60 0xfc01f07ff001f8c3 0x59ac009f05f80ce0

def z820 : W := mkw 0x53a0008400004003 0xe03ffbfbf8200240 0xfffe0ffc7e39c7fb 0xfdfffffffa3983f3

def z821 : W := mkw 0x13a0000000000002 0x203febeb78000000 0xfc3e000000000003 0x603fe7ff78000000

def z822 : W := mkw 0xc80139cd2001e400 0x008700ed01680f60 0xfc00007ff00038c1 0x088f009f01f80ce0

def z823 : W := mkw 0x13a0000000000001 0xe00f9b5bf8000000 0xfffe000000000001 0x200f1f1ff8000000

def z824 : W := mkw 0x0200000000000002 0x003fe9e928000000 0xfffe000000000003 0xe03ffffff8000000

def z825 : W := mkw 0xc000108c0000c000 0x0002004c01200a60 0xfffffffffff9ffff 0xfdffe0ffffff8fff

def z826 : W := mkw 0xa5c8502884448891 0xcd089a16d18458b8 0xfffff07f8fc7f8ff 0xffacff9ffdc67cfc

def z827 : W := mkw 0x1321ce724f200002 0x323deda36edfb000 0x1ffffffffffe0003 0xfe3fffe7fffff000

def z828 : W := mkw 0x13a1486004000003 0xf03ffbfbfecc1000 0xffffffffffc60003 0xfe3ffffffffe7000

def z829 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc00007ff00000c1 0x088f001f01f800e0

def z830 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc00000000000001 0x000f1f1f00000000

def z831 : W := mkw 0x13a0000000000001 0xe00ffb5bf8000000 0xfc06000000000001 0x200f3f1f18000000

def z832 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffe0f800e39c73b 0xf57ffffffa018313

def z833 : W := mkw 0x13b4a50008911223 0xf03dfbb3fe028505 0x1ffff0000ff8383c 0xa46cff87fc078c1f

def z834 : W := mkw 0x12b4a50008911222 0x303763e93e028505 0xfc07ff800039ff03 0x717f27ff1e018f03

def z835 : W := mkw 0x37e8402084440893 0xed3ffbfbf8845098 0xfffff0000fc7f83f 0xf73ffffffc067c1c

def z836 : W := mkw 0xc000108c0000c000 0x0002004c01200a60 0xfc000ffff001c7c3 0x599f007f03f803e0

def z837 : W := mkw 0xe5ca108c904ec9d9 0xcd02125ed1204afa 0xfff800000001f8fc 0x4180009fe0000cfc

def z838 : W := mkw 0x0214a50008911222 0x103561a02e028505 0x03ffff800ff9ff3e 0xf573e7e0fe078f1f

def z839 : W := mkw 0x11a0402004000001 0xe00f9b5bd0841000 0xfc00007f80060001 0x0a0f1f1f01c07000

def z840 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff001ffc1 0x19af009f07f80fe0

def z841 : W := mkw 0x71e20294120a4149 0xed02165bd03162d2 0xffc60ffc7e3fc7fb 0xffd33f7f9a39f3f3

def z842 : W := mkw 0xca159ccd2890f620 0x0087604d296a8a65 0xfffe007ffff800fd 0xaccfe01ff9ff80ff

def z843 : W := mkw 0x25ca4230964e09d9 0xcd089e12d095709a 0x03ffff800fffff3e 0xf770ffe0fe07ff1f

def z844 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x00000ffff0060003 0x1a1f1f0003f87000

def z845 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0007ffffffffff03 0xff7fffe01fffff03

def z846 : W := mkw 0xdab5bdcd2891f622 0x30b763ed3f6a8f65 0xfffffffffff9ffff 0xfdffe7ffffff8fff

def z847 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xffc60f800e39c73b 0xf55f3f7f9a018313

def z848 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfff9f07fffc1f8ff 0xddafc09fe5fe0cfc

def z849 : W := mkw 0x4000029402004000 0x0002044800312240 0xe3c60ffc7e3fc7fb 0xffd33f789a39f3f3

def z850 : W := mkw 0x13a18c4249200003 0xf23ffbfbfe4a8000 0xfffe000000000003 0xe03ffffff8000000

def z851 : W := mkw 0x8000502804008000 0x0008880401841820 0xfff9f07f8fc7f8ff 0xdfacd89fe5c67cfc

def z852 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0000007ffe060003 0x9e0f1f0001f87000

def z853 : W := mkw 0x11a0000000000001 0xe002125bd0000000 0xfc00000000000001 0x00031f1f00000000

def z854 : W := mkw 0xc815bdcd2891f622 0x10b700ed076a8f65 0xfc01fffff1c1ffc7 0x59bf00ff07fe0fec

def z855 : W := mkw 0x0509ce72cf640892 0x123ded0246dfb008 0x0039fffffffe0007 0x9e3fff0067fff00c

def z856 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0039ffffffffff07 0xdf3fffe067ffff0c

def z857 : W := mkw 0x8001184800008000 0x0005000401480820 0xfc01f07ff001f8c3 0x59af009f05f80ce0

def z858 : W := mkw 0xc80139cd2001e402 0x10bde90407680f60 0x0001fffff001ffc3 0x99bfff0007f80fe0

def z859 : W := mkw 0x8001184800008002 0x103700ed07480820 0xfc01fffff001f8c3 0x59bf00ff07f80ce0

def z860 : W := mkw 0xc800f7bf6f21e400 0x028aeded01b7bf60 0xfc0000000fffffc0 0xc780ffff0007ffe0

def z861 : W := mkw 0x0180000000000001 0xc00a9a5ad0000000 0xfc00000000000001 0x000f1f1f00000000

def z862 : W := mkw 0x0101ce724f200002 0x123ded0246dfb000 0x1c39fffffffe0003 0x9e3fff8767fff000

def z863 : W := mkw 0x1335ef724fb11222 0x323deda36edfb505 0x1fffffffffffff3f 0xff7fffe7ffffff1f

def z864 : W := mkw 0x0000021002000000 0x0000040000112000 0x0001fffffe3e0003 0x9e3f3f0007f9f000

def z865 : W := mkw 0x0000423006000000 0x00088c0000953000 0x03ffffffffffff3f 0xff7fffe0ffffff1f

def z866 : W := mkw 0x13a0000000000003 0xe03773fbf8000000 0xfc06000000000000 0x2013277f18000000

def z867 : W := mkw 0x13a0000000000001 0xe00f9bfbf8000000 0xfffe000000000003 0xe02fdffff8000000

def z868 : W := mkw 0xe8431add320ae548 0x0d80040401796af2 0x00000ffffe3fc7f8 0x1fc0000003f9f3f3

def z869 : W := mkw 0xc80118cd2000e402 0x00b700ed01680a60 0xfc000ffff001c7c3 0x59bf00ff03f803e0

def z870 : W := mkw 0x13a1cc624d200003 0xf23ffbfbfece9000 0xfffff07f8fc60003 0xfe3ffffffdc67000

def z871 : W := mkw 0xc80118cd2000e400 0x008700ed01680a60 0xfc00007ff00000c1 0x488f00ff01f800e0

def z872 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f0038fc7f8fc 0xc7acd89fe5c67cfc

def z873 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xffffff800ff9ff3f 0xf57ffffffe078f1f

def z874 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0039ffffffffff3f 0x9f7fff8067ffff1f

def z875 : W := mkw 0x13a0000000000003 0xe038fbb2f8000000 0xfffe000000000003 0xe03cfffff8000000

def z876 : W := mkw 0xf7ea108c904ec9d9 0xed0212fff9204afa 0xfffe00000001fffc 0x61c000fff8000fff

def z877 : W := mkw 0x11a0000000000003 0xe03f9bfbd0000000 0xfc00000000000001 0x001f1f7f00000000

def z878 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffff00001c03807 0xe03ffffffc060c0c

def z879 : W := mkw 0x0000000000000000 0x000f894900000000 0xfc00000000000001 0x000f1f1f00000000

def z880 : W := mkw 0x13a0000000000003 0xe03afbfbf8000000 0xfffe000000000002 0xe030fffff8000000

def z881 : W := mkw 0xa448523886448890 0x0d000404019578b8 0x0001fffffffff8fc 0x1f80000007fffcfc

def z882 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfffff07f8fc7f8ff 0xffbcf8fffdc67cfc

def z883 : W := mkw 0xc815bdcd2891f622 0x10b700ed076a8f65 0xfff9fffffff9ffff 0xddffc0ffe7ff8fff

def z884 : W := mkw 0x13a0000000000003 0xe03773fbf8000000 0xfffe000000000002 0xe033e7fff8000000

def z885 : W := mkw 0x13a0000000000001 0xe00a9bfbf8000000 0xfffe000000000000 0x60001ffff8000000

def z886 : W := mkw 0x53a0008400004003 0xe03ffbfbf8200240 0xfffe0f8070000703 0xe03ffffffa380300

def z887 : W := mkw 0x13a0000000000001 0xe00273fbf8000000 0xfffe000000000000 0x600027fff8000000

def z888 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc00007ff00000c3 0x48af009f01f800e0

def z889 : W := mkw 0x2548c632cf640891 0xcf089c12c097f098 0x03f800000ffe003c 0x8600d800e007f01c

def z890 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe0060ffc7e3fc7f9 0x3fd33f781a39f3f3

def z891 : W := mkw 0xca0139cd2001e402 0x10b760ed2f680f60 0xfc39fffff001ffc3 0x59bfc0ff67f80fe0

def z892 : W := mkw 0xc000108c0000c002 0x003700ed01200a60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z893 : W := mkw 0xc80118cd2000e402 0x00b700ed01680a60 0xfc00007ff00000c1 0x089f007f01f800e0

def z894 : W := mkw 0x0001ce724f200000 0x020d8d0000dfb000 0x0000007ffffe0001 0x0e0f1f0001fff000

def z895 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xffffff800039ff03 0xf17ffffffe018f03

def z896 : W := mkw 0x400108c400004002 0x103700e906680240 0xfc01fffff001c7c3 0x59bf00ff07f803e0

def z897 : W := mkw 0x0080000000000001 0xc007125990000000 0xfc00000000000001 0x000f1f1f00000000

def z898 : W := mkw 0x0000423006000000 0x00088c0000953000 0x0000007ff0060001 0x0a0f1f0001f87000

def z899 : W := mkw 0x0200000000000002 0x003060a028000000 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z900 : W := mkw 0xca1539cd2091f620 0x008700ed29680f65 0xfffe007ff001fffd 0x69cf00fff9f80fff

def z901 : W := mkw 0xc815ffff6fb1f620 0x1280040407ffbf65 0x0001fffffffffffc 0x1fc0000007ffffff

def z902 : W := mkw 0x11a0000000000001 0xe002125bd0000000 0xffc6000000000003 0xe0133f7f98000000

def z903 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff00007c3 0x18bf007f07f803e0

def z904 : W := mkw 0xe843ffff7f2be548 0x1f80040407fffff2 0x0001fffffffffff8 0x1fc0000007fffff3

def z905 : W := mkw 0x0100000000000001 0xc00d9912c0000000 0xfff8000000000003 0xc02fdf9fe0000000

def z906 : W := mkw 0x1335ef724fb11222 0x323deda36edfb505 0x1c39fffffffe3807 0x9e3fff8767fffc0c

def z907 : W := mkw 0xa449de7acf648890 0x1f00040407dff8b8 0x0001fffffffe00c0 0x1e80000007fff0e0

def z908 : W := mkw 0xc815bdcd2891f622 0x10b700ed076a8f65 0xffc7fffffff9ffff 0xfdff20ff9fff8fff

def z909 : W := mkw 0x0215ef724fb11222 0x123ded002edfb505 0x03ffffffffffff3f 0xbf7fff00ffffff1f

def z910 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffffe39ffc3 0xddbf20ff07f98fe0

def z911 : W := mkw 0xc80139cd2001e400 0x108200ed07680f60 0xfc01fffff001ffc3 0x59ac00ff07f80fe0

def z912 : W := mkw 0x13a0000000000001 0xe00afb5af8000000 0xfffe000000000003 0xe03ffffff8000000

def z913 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe007c0e060003 0xfe3ffffff8007000

def z914 : W := mkw 0x11a0000000000001 0xe00f9bfbd0000000 0xfc00000000000001 0x400f1fff00000000

def z915 : W := mkw 0xe45ef7bc9edfdbf8 0x1d00040407b7ffff 0x0001fffffffffffc 0x1fc0000007ffffff

def z916 : W := mkw 0xc80118cd2000e402 0x00b7004d01680a60 0xfc00007ff00000c3 0x08bf001f01f800e0

def z917 : W := mkw 0x13a0840008000003 0xf03ffbfbfe028000 0xfffff00001c00003 0xe03ffffffc060000

def z918 : W := mkw 0x00014a7247200002 0x123ded0006dd3000 0x0001fffff0060003 0x9a3fff0007f87000

def z919 : W := mkw 0xca0139cd2001e402 0x10b760ed2f680f60 0xfc07fffff001ffc3 0x79bf20ff1ff80fe0

def z920 : W := mkw 0x00018e500a000002 0x10356400065ba000 0x0001fffffffe0003 0x9e3fff0007fff000

def z921 : W := mkw 0xec49ffffef65ec90 0x1f80040407fffff8 0x0001fffffffffffc 0x1f80000007fffffc

def z922 : W := mkw 0xec4b7bfdb64fedd8 0x1d80040407fd7ffa 0x0001fffffffffffc 0x1fc0000007ffffff

def z923 : W := mkw 0x13a1294000010003 0xf03ffbfbfe480500 0xfffffffff001ff03 0xf93ffffffff80f00

def z924 : W := mkw 0xc800318d2001e400 0x008200ed01200f60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z925 : W := mkw 0xe44a52bc964ec9d8 0x0d00040401b57afa 0x00000ffffe3fc7f8 0x1fc0000003f9f3f3

def z926 : W := mkw 0x0000000000000002 0x003de9a100000000 0x1c00000000000003 0x803fff8700000000

def z927 : W := mkw 0xc88139cd2001e401 0xd082125c97680f60 0xe3c7fffff001ffc3 0xf9933f789ff80fe0

def z928 : W := mkw 0x0201ce724f200002 0x123deda02edfb000 0x0007fffffffe0003 0xbe3fff601ffff000

def z929 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0007fffffffe0703 0xbe7fff601ffff303

def z930 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01f07ff001ffc1 0x49af00ff05f80fe0

def z931 : W := mkw 0x13a0402004000003 0xe03ffbfbf8841000 0xfffe007f80060003 0xea3ffffff9c07000

def z932 : W := mkw 0x0180000000000001 0xc002125ad0000000 0xfffe000000000003 0xe0133ffff8000000

def z933 : W := mkw 0xc80118cd2000e402 0x00b700ed01680a60 0xfc01f07ff001f8c3 0x59bf00ff05f80ce0

def z934 : W := mkw 0xc88139cd2001e402 0x10b702ed17680f60 0xfc07fffff001ffc3 0x79bf27ff1ff80fe0

def z935 : W := mkw 0x13b4e5200c911223 0xf03ffbfbfe869505 0xffffffff8fffff3f 0xff7fffffffc7ff1f

def z936 : W := mkw 0x0000000000000002 0x003761e900000000 0xfc00000000000003 0x403f27ff00000000

def z937 : W := mkw 0x0015ef724fb11222 0x123ded0006dfb505 0x0001fffffffe0703 0x9e7fff0007fff303

def z938 : W := mkw 0x13b4210000911223 0xe03ffbfbf8000505 0xfffff0000fc1ff3f 0xf57ffffffc060f1f

def z939 : W := mkw 0x13b4a50008911223 0xe03ffbfbf8028505 0xfffe00000ff9ff3f 0xe57ffffff8078f1f

def z940 : W := mkw 0x13b4a50008911223 0xf03773fbfe028505 0xfffe0f800039ff3c 0x615327fffa018f1f

def z941 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfc00000000000003 0x402f1f9f00000000

def z942 : W := mkw 0x33e0000000000003 0xed3ffbfbf8004090 0xfffff07c0fc7f8ff 0xffbffffffc067cfc

def z943 : W := mkw 0xdba139cd2001e401 0xf088fb16ff680f60 0x03fffffff001ffc0 0xb980ff00fff80fe0

def z944 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0000007ff0060001 0x0a0f1f0001f87000

def z945 : W := mkw 0x871dfd6acdf59ab2 0x123de9a66fce9d2d 0x1c39f00381c03804 0x002cc08765c60c0c

def z946 : W := mkw 0x13a0000000000003 0xe03272fbf8000000 0xfffe000000000003 0xe033fffff8000000

def z947 : W := mkw 0xc80118cd2000e402 0x10b7004d07680a60 0xfc01f07ff00000c1 0x08af001f05f800e0

def z948 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc07fffffff9ffc3 0xfdffe0ff1fff8fe3

def z949 : W := mkw 0xe44a52bc964ec9d8 0x0d00040401b57afa 0x0000007ff00600c0 0x0a80000001f870e0

def z950 : W := mkw 0x13a0c4224d200003 0xe23ffbfbf8869000 0xfffe000001c00003 0xe03ffffff8060000

def z951 : W := mkw 0xca0139cd2001e402 0x10b760ed2f680f60 0xfffffffffe39fffb 0xfdffe0fffff98ff3

def z952 : W := mkw 0x00010a5002000000 0x1000040006592000 0x0001fffffe3e0003 0x9e133f0007f9f000

def z953 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc06000000000003 0xa03fff7f18000000

def z954 : W := mkw 0xa040100800008001 0xcd001014810048b0 0xfff9f07f8fc7f8ff 0xdfacd89fe5c67cfc

def z955 : W := mkw 0x11a0000000000003 0xe03ffb5bd0000000 0xfc00000000000001 0x002fdf1f00000000

def z956 : W := mkw 0x0015ce724fb01222 0x123ded0006dfb005 0x0001fffffffe003f 0x9e7fff0007fff01f

def z957 : W := mkw 0xa65dff7acff59ab2 0x1f3064a42fdffdbd 0x03fffffffffffffe 0xfff0e0e0ffffffff

def z958 : W := mkw 0x0000423006000002 0x003ded0000953000 0x0001fffffffe0003 0x9e3fff0007fff000

def z959 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000001 0x601f3ffff8000000

def z960 : W := mkw 0xc88339cd300be54a 0x10b702ed17680f62 0xfc07fffff001ffc3 0x79ff00ff1ff80fe3

def z961 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fffffc0fffff3f 0xff70f8e0fe07ff1f

def z962 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffff07f80000003 0xf83ffffffdc00000

def z963 : W := mkw 0x61c20294120a4149 0xcd02165ad03162d2 0xfffe0ffc7e3fc7fb 0xffd33ffffa39f3f3

def z964 : W := mkw 0xa548502884448890 0x0d088806418458b8 0xfc39f07f8fc7f8ff 0x5facc09f65c67cfc

def z965 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffff1fe0001 0x0a3fff0007fff000

def z966 : W := mkw 0x5bb5adc528917623 0xf0bffbfbfe6a8745 0xfffe0f8070380703 0xe07ffffffa398303

def z967 : W := mkw 0x0214840008901220 0x0000600028028005 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z968 : W := mkw 0x8801ff7b6f21a400 0x1280040407dfbd20 0x0001fffffffe3800 0x1e00000007fffc00

def z969 : W := mkw 0x0080000000000001 0xc002125890000000 0xffc6000000000003 0xe03f3fff98000000

def z970 : W := mkw 0x13a1486245200003 0xe23ffbfbf8cc1000 0xfffe000380000003 0xe03ffffff9c00000

def z971 : W := mkw 0x1320000000000002 0x203de9a368000000 0x1c38000000000000 0x003fe78760000000

def z972 : W := mkw 0xb5e8502884448891 0xed089b16d18458b8 0xfff9f07f8fc7f8ff 0xdfacdf9fe5c67cfc

def z973 : W := mkw 0x13b5ed624db11223 0xf23ffbfbfece9505 0xfffff00381c03807 0xe03ffffffdc60c0c

def z974 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfc00000000000003 0x801f3f1f00000000

def z975 : W := mkw 0xdaa118cd2000e402 0x20b763ed39680a60 0xfc06007ff00000c1 0x289f277f19f800e0

def z976 : W := mkw 0xc80139cd2001e400 0x1087004d07680f60 0xfc01fffff001ffc3 0x599f007f07f80fe0

def z977 : W := mkw 0xb6e8502884448892 0x2d3763ed398458b8 0x0007f07f8fc7f8fc 0x3f9327601dc67cfc

def z978 : W := mkw 0x13a0000000000001 0xe00afbfbf8000000 0xfffe000000000003 0xe02cfffff8000000

def z979 : W := mkw 0x73e20084100a414b 0xed3ffbfbf82042d2 0xfffe0000000000c3 0xe0bffffff80000e0

def z980 : W := mkw 0x25484232c7640891 0xcf089d12c0957098 0x03f800000fc6003c 0x8600df00e006701c

def z981 : W := mkw 0x11a0000000000001 0xe00a9b5bd0000000 0xfc00000000000000 0x00001f1f00000000

def z982 : W := mkw 0x0215ad4008911222 0x103560a02e4a8505 0x03ffff807ff9ff3e 0xf573e0e0fe3f8f1f

def z983 : W := mkw 0x0000c6300e000002 0x1038ec000697b000 0x0001fffffffe0003 0x9e3fff0007fff000

def z984 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffff0000ff8383f 0xe47ffffffc078c1f

def z985 : W := mkw 0xca15ffff6fb1f622 0x12b064a42fffbf65 0x03fffffffffffffe 0xfff0e0e0ffffffff

def z986 : W := mkw 0xe8c2318d300be549 0xcd8212fd91204ff2 0xfc0000000001ffc0 0x418000ff00000fe0

def z987 : W := mkw 0x13b4a50008911223 0xf038fbb2fe028505 0xffffff800ff9ff3f 0xf57cfffffe078f1f

def z988 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfff9f0000fc1f83f 0xd52fdf9fe4060c1c

def z989 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xffffff800ff80703 0xf47ffffffe078303

def z990 : W := mkw 0xdaa139cd2001e402 0x30b702ed3f680f60 0xfc07fffff001ffc3 0x79bf00ff1ff80fe0

def z991 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc07fffff039ffc3 0x79ff20ff1ff98fe3

def z992 : W := mkw 0x13a0000000000002 0x203febeb78000000 0x1c06000000000000 0x201f276718000000

def z993 : W := mkw 0x13a0402004000003 0xe03ffbfbf8841000 0xfffff07f8fc7f83f 0xff3ffffffdc67c1c

def z994 : W := mkw 0xe5ca108c904ec9d9 0xcd02125ed1204afa 0xfc000000000000c0 0x0080001f000000e0

def z995 : W := mkw 0x13a1084000000003 0xe03ffbfbf8480000 0xfffe007ff0000003 0xe83ffffff9f80000

def z996 : W := mkw 0x13a0000000000001 0xe00dfb13f8000000 0x1ffe000000000000 0xa00cff07f8000000

def z997 : W := mkw 0x25cac632df6e09d9 0xcf08ff12d097f09a 0x03fe00000ffe003c 0xa640ff00f807f01f

def z998 : W := mkw 0xe857bfdd3a9bf768 0x1d800404077beff7 0x0001fffffffffffc 0x1fc0000007ffffff

def z999 : W := mkw 0xa44a5238964e89d8 0x0d000404019578ba 0x0001f07f8ffff8fc 0x1fc0000005c7fcff

def z1000 : W := mkw 0x11a0000000000003 0xe03ffb5bd0000000 0xffc6000000000003 0xe03fff7f98000000

def z1001 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc00007ff001c0c3 0x598f001f01f800e0

def z1002 : W := mkw 0x1120000000000000 0x200d890340000000 0x1c00000000000001 0x000f1f0700000000

def z1003 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffffe39fffb 0x5dff00ff07f98ff3

def z1004 : W := mkw 0x60420294120a414a 0x0d3704e9003162d2 0xfc000ffc7e3fc7fb 0x5fff00ff0239f3f3

def z1005 : W := mkw 0x0001ce724f200000 0x120d8d0006dfb000 0x00000ffff03e0001 0x0a0f1f0003f9f000

def z1006 : W := mkw 0x0000000000000002 0x003f89e900000000 0xfc00000000000003 0x403f1fff00000000

def z1007 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe0060ffc7e3e07c3 0xbed33f781a39f3e3

def z1008 : W := mkw 0x13a0000000000002 0x203763eb78000000 0x1c3e000000000000 0x201327e778000000

def z1009 : W := mkw 0x1334a50008911222 0x303de9a36e028505 0x1c39ff800ff83807 0x943fff8766078c0c

def z1010 : W := mkw 0x1320000000000003 0xe03df9b3e8000000 0xfff8000000000003 0xc03fff9fe0000000

def z1011 : W := mkw 0x0080000000000001 0xc00212f990000000 0xffc6000000000003 0xe0133fff98000000

def z1012 : W := mkw 0x0001ef724f210002 0x123ded0006dfb500 0x0001ffffffffff03 0x9f3fff0007ffff00

def z1013 : W := mkw 0x00016b7247210002 0x123d8da006dd3500 0x0001fffff007ff03 0x5b3f1fe007f87f00

def z1014 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfffffffffff9ffff 0xfdffe0ffffff8fff

def z1015 : W := mkw 0x0180000000000001 0xc00a9a5ad0000000 0xfff8000000000003 0xc02fdf9fe0000000

def z1016 : W := mkw 0xc80139cd2001e400 0x0087004d01680f60 0xfc00007ff001ffc1 0x098f001f01f80fe0

def z1017 : W := mkw 0x8001184800008000 0x0005000401480820 0xfc00007ff00000c1 0x088f001f01f800e0

def z1018 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x03fffffffffe073f 0xbe7fff60fffff31f

def z1019 : W := mkw 0x11a1cc624d200003 0xf23ffb5bd6ce9000 0xfc01f00381c00001 0x002fdf1f05c60000

def z1020 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9ffff8fffffff 0xdfecd89fe7c7ffff

def z1021 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01ffffffc1ffc3 0xddbfc0ff07fe0fe0

def z1022 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03ffffff8ff9ff3f 0xfd7ce0e0ffc78f1f

def z1023 : W := mkw 0x61420294120a4149 0xcd089c12c03162d2 0xfff80ffc7e3fc7fb 0xdfecd89fe239f3f3

def z1024 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffe0f800039ff3f 0xe17ffffffa018f1f

def z1025 : W := mkw 0x8001184800008000 0x1000000407480820 0xfc01fffff001f8c3 0x59ac009f07f80ce0

def z1026 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffffffff83f 0x9f3fff0007fffc1c

def z1027 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe007c0001c0c3 0xf9bffffff80000e0

def z1028 : W := mkw 0x73e20084100a414b 0xed3ffbfbf82042d2 0xfffe0f800e39c7fb 0xf5fffffffa0183f3

def z1029 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xffc6000000000003 0xe01f3f7f98000000

def z1030 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffff03e0003 0x1a3f3f0007f9f000

def z1031 : W := mkw 0x1ba1294120012403 0xf0bffbfbfe480500 0xfffe000000000003 0xe03ffffff8000000

def z1032 : W := mkw 0x13a0000000000001 0xe008fb12f8000000 0xfffe000000000000 0xe000ff9ff8000000

def z1033 : W := mkw 0x60420294120a4148 0x0d000400003162d2 0x03c60ffc7e3fc7fb 0xffd33f609a39f3f3

def z1034 : W := mkw 0x13a0000000000001 0xe008fbb3f8000000 0x1ffe000000000000 0xa000ff87f8000000

def z1035 : W := mkw 0x53a108c400004003 0xf03ffbfbfe680240 0xfffffffff001c7c3 0xf9bffffffff803e0

def z1036 : W := mkw 0x13a0000000000003 0xe03712fbf8000000 0xfffe000000000003 0xe03f3ffff8000000

def z1037 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xffc60ffffe39c7fb 0xfddf207f9bf983f3

def z1038 : W := mkw 0x1320000000000002 0x203de9a368000000 0x1c38000000000001 0x002fdf8760000000

def z1039 : W := mkw 0x0015ef724fb11222 0x123deda006dfb505 0x0001ffffffffff3f 0xdf7fffe007ffff1f

def z1040 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc01f07ff00038c1 0x08af009f05f80ce0

def z1041 : W := mkw 0x51a0008400004001 0xe00f9b5bd0200240 0xfc000ffc7001c7c3 0x599f1f7f023803e0

def z1042 : W := mkw 0x0001ce724f200000 0x120ded0006dfb000 0x0001fffffffe0001 0x9e0fff0007fff000

def z1043 : W := mkw 0x13a0000000000003 0xe03773fbf8000000 0xfffe000000000003 0xe0133ffff8000000

def z1044 : W := mkw 0x65ca0294924e49d9 0xcd02165ad03162da 0xe3fe0ffc7e3fc7ff 0xffd33f78fa39f3ff

def z1045 : W := mkw 0x10a0000000000000 0x2007034910000000 0xfc00000000000001 0x000f071f00000000

def z1046 : W := mkw 0x0001ce724f200002 0x1230640006dfb000 0x0001fffffffe0003 0x9e33ff0007fff000

def z1047 : W := mkw 0x25ca4230964e09d9 0xcd089e12d095709a 0x0000000000060000 0x02001f0000007000

def z1048 : W := mkw 0xa45dff7acff59ab0 0x1f00040407dffdbd 0x0001fffffffffffc 0x1fc0000007ffffff

def z1049 : W := mkw 0x13b4a50008911223 0xf03272fbfe028505 0xffffff800ff9ff3f 0xf573fffffe078f1f

def z1050 : W := mkw 0x80019c4808008002 0x10356004074a8820 0xfff9fffffff9f8ff 0xddbfe09fe7ff8cfc

def z1051 : W := mkw 0x0000c6324f200000 0x0208ed000097b000 0x0001fffffffe0003 0x9e3fff0007fff000

def z1052 : W := mkw 0xc00118cc0000c002 0x1037004c07680a60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z1053 : W := mkw 0xe842339d320be548 0x0d80040401316ff2 0x00000ffc7e3ffff8 0x1fc000000239fff3

def z1054 : W := mkw 0xc000108c0000c000 0x0002004c01200a60 0xfc00007ff00000c1 0x088f001f01f800e0

def z1055 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x03f9fffffffff83f 0xdf3fff80e7fffc1c

def z1056 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc39fffffff9ffc7 0xddbfe0ff67ff8fec

def z1057 : W := mkw 0x0001ce724f200002 0x1235650006dfb000 0x0001fffffffe0003 0x9e133f0007fff000

def z1058 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01ff83f001ffc0 0x41bf00ff07f80fe0

def z1059 : W := mkw 0x13a0840008000003 0xf03ffbfbfe028000 0xffffff800ff9c73b 0xf57ffffffe078313

def z1060 : W := mkw 0x13b4840008901223 0xf03ffbfbfe028005 0xffffff800ff8003f 0xf47ffffffe07801f

def z1061 : W := mkw 0x0015ef724fb11222 0x123ded0006dfb505 0x0001fffffffe3807 0x9e3fff0007fffc0c

def z1062 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc000ffff00007c3 0x48bf00ff03f803e0

def z1063 : W := mkw 0x13a0210000010003 0xf03ffbfbfe000500 0xffffff800fc1ff3f 0xf53ffffffe060f1c

def z1064 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0007ffffffffff3f 0xbf7fff601fffff1f

def z1065 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001ffffffffc703 0xdf3fff6007fff300

def z1066 : W := mkw 0x880139492001a402 0x10b500a507480d20 0xfc01fffff001f8c3 0x59bf009f07f80ce0

def z1067 : W := mkw 0x13a0840008000003 0xe03ffbfbf8028000 0xfffe00000ff80003 0xe43ffffff8078000

def z1068 : W := mkw 0x4a15afd76bb17622 0x12b765e92e7ba745 0x00060f8070380700 0x205327601a398303

def z1069 : W := mkw 0x11a1084000000003 0xf03f9b5bd6480000 0xfc01fffff0000003 0x183f1f1f07f80000

def z1070 : W := mkw 0x1321ce724f200002 0x323ded026edfb000 0x0039fffffffe0003 0x9e3fff0067fff000

def z1071 : W := mkw 0x275cc632cff41ab1 0xcf08fd12e897f09d 0x03fe00000ffe003c 0xa640ff00f807f01f

def z1072 : W := mkw 0x13b4840008901221 0xe008fb12f8028005 0xfffff0000ff9f83f 0xf56cff9ffc078c1f

def z1073 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001f07ffffe0001 0x8e2fff0005fff000

def z1074 : W := mkw 0x37ea4230964e09d9 0xed08ff12f895709a 0x03fe00000ffe003c 0xa640ff00f807f01f

def z1075 : W := mkw 0xca15bdcd2891f622 0x10b060a42f6a8f65 0xfffffffffff9ffff 0xfdfce0ffffff8fff

def z1076 : W := mkw 0x8409de7acf648890 0x1200040407dfb828 0x0001fffffffe3804 0x1e00000007fffc0c

def z1077 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f07f8fc7f8ff 0xdfbfff9fe5c67cfc

def z1078 : W := mkw 0x33e20000100a014b 0xed3ffbfbf8004092 0xfffe00000000003b 0xe07ffffff8000013

def z1079 : W := mkw 0xc80139cd2001e400 0x1082004c07680f60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z1080 : W := mkw 0x0300000000000003 0xc03df9b2e8000000 0xfffe000000000003 0xe03ffffff8000000

def z1081 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c60f807e3fc7f8 0xe7d33f789a39f3f3

def z1082 : W := mkw 0xca0118cd2000e402 0x00b760ed29680a60 0xfffe007ff00000c3 0xe8bfe0fff9f800e0

def z1083 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc000ffff001c7c1 0x198f001f03f803e0

def z1084 : W := mkw 0x11a0000000000003 0xe03f9bfbd0000000 0xfc00000000000001 0x002f1f9f00000000

def z1085 : W := mkw 0x1320000000000002 0x203de9a368000000 0x1ffe000000000003 0xe03fffe7f8000000

def z1086 : W := mkw 0x53a20084100a414b 0xe03ffbfbf8200242 0xfffe000000000703 0xe07ffffff8000303

def z1087 : W := mkw 0x13a0000000000001 0xe00212fbf8000000 0xfffe000000000000 0x601327fff8000000

def z1088 : W := mkw 0x8001de7a4f208000 0x1200040407dfb820 0x0001fffffffff8c0 0x1f80000007fffce0

def z1089 : W := mkw 0x1334a50008911222 0x303de9a36e028505 0x1fffff800ff9ff3f 0xf57fffe7fe078f1f

def z1090 : W := mkw 0xca0139cd2001e402 0x10b760ed2f680f60 0xffffffffffc1ffff 0xfdbfe0fffffe0ffc

def z1091 : W := mkw 0x0214a50008911220 0x100000a02e028505 0x03ffff800ff9ff3e 0xf560c0e0fe078f1f

def z1092 : W := mkw 0x13a0000000000002 0x203febeb78000000 0x1c3e000000000003 0xa03fffe778000000

def z1093 : W := mkw 0x00010a5002000002 0x1035040006592000 0x0001fffff0060003 0x1a3f1f0007f87000

def z1094 : W := mkw 0x37fcc4208cd41ab3 0xed3ffbfbf886d09d 0xfffe00000ffe003f 0xe67ffffff807f01f

def z1095 : W := mkw 0xc80139cd2001e402 0x10b760ed07680f60 0xfc01fffff001ffc3 0xd9bfe0ff07f80fe0

def z1096 : W := mkw 0x13a0000000000001 0xe00afb5bf8000000 0xfffe000000000000 0xa000ff1ff8000000

def z1097 : W := mkw 0xca01bdcd2801e402 0x10b760ed2f6a8f60 0xfffffffffff9ffc3 0xfdbfe0ffffff8fe0

def z1098 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x03f9f07fffc7f83f 0xdf2fdf80e5fe7c1c

def z1099 : W := mkw 0x73e0008400004003 0xed3ffbfbf82042d0 0xfffe0ffc7e07c7fb 0xffbffffffa3873f0

def z1100 : W := mkw 0x0215ce724fb01222 0x123ded002edfb005 0x03fffffffffff83f 0xff7fff80fffffc1f

def z1101 : W := mkw 0x13a0000000000003 0xf03ffbfbfe000000 0xffffff8000000003 0xf03ffffffe000000

def z1102 : W := mkw 0x13b4a50008911221 0xe00afbfbf8028505 0xfffe00000ff9ff3c 0xe540fffff8078f1f

def z1103 : W := mkw 0xc80139cd2001e400 0x1080000407680f60 0xfc01fffff001ffc1 0x198c001f07f80fe0

def z1104 : W := mkw 0x13a0000000000003 0xe03f9bfbf8000000 0xfffe000000000003 0x603f1ffff8000000

def z1105 : W := mkw 0xe8c2108d300ae549 0xcd82125d91204af2 0xfc000000000000c0 0x0080001f000000e0

def z1106 : W := mkw 0x0214210000911220 0x000000a028000505 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z1107 : W := mkw 0x5ba0218520016403 0xe0bffbfbf8200740 0xfffe000000000703 0xe03ffffff8000300

def z1108 : W := mkw 0xc8017bff6721e400 0x1280040407fd3f60 0x0001fffff007ffc0 0x1b80000007f87fe0

def z1109 : W := mkw 0x27dee7309edf1bfb 0xdd38feb2fe97f59f 0x03ffff800fffff3e 0xf770ffe0fe07ff1f

def z1110 : W := mkw 0x13a0000000000003 0xe03773fbf8000000 0xfffe000000000003 0x603f27fff8000000

def z1111 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0001f07fffc60001 0x1e0f1f0005fe7000

def z1112 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfff8000000000001 0x800fdf1fe0000000

def z1113 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffe0f800ff8073f 0xe47ffffffa07831f

def z1114 : W := mkw 0xc80139cd2001e402 0x10b500a507680f60 0xfc01fffff001ffc3 0x59ac009f07f80fe0

def z1115 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0xfc01fffffffe0003 0xde3fff9f07fff000

def z1116 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc38000000000003 0x803fff9f60000000

def z1117 : W := mkw 0x0180000000000003 0xc03ffb5ad0000000 0xfffe000000000003 0xe03ffffff8000000

def z1118 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000000 0xe013fffff8000000

def z1119 : W := mkw 0x2548c632cf640893 0xdf38fd12c697f098 0x03f9ff800ffff83e 0xd730ff80e607fc1c

def z1120 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03ffff800ff9ff3f 0xf573ffe0fe078f1f

def z1121 : W := mkw 0x11a0840008000003 0xf03ffb5bd6028000 0xfc01ff800ff80003 0x943fff1f06078000

def z1122 : W := mkw 0xca1539cd2091f622 0x10b700ed2f680f65 0xfc07fffff001ffc3 0x79ff00ff1ff80fe3

def z1123 : W := mkw 0x8508502884448890 0x0008880641841828 0xfc39f07f8fc7f8c7 0xdfacd89f65c67cec

def z1124 : W := mkw 0x11a0000000000001 0xe00ffb5bd0000000 0xfc00000000000001 0x800fff1f00000000

def z1125 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c7fffc7fffffff 0xffd33f789e3fffff

def z1126 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe00000e38003b 0xe47ffffff8018013

def z1127 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01f07ff00038c3 0x48bf00ff05f80ce0

def z1128 : W := mkw 0x13a0210000010003 0xf03ffbfbfe000500 0xfffff00000003803 0xe03ffffffc000c00

def z1129 : W := mkw 0x0214a50008911222 0x103060a02e028505 0xffffff800ff9ff3f 0xf57ce0fffe078f1f

def z1130 : W := mkw 0x0180000000000001 0xc0089a12d0000000 0xfffe000000000003 0xe02cff9ff8000000

def z1131 : W := mkw 0x8a15fd6b6db1b622 0x12bde9a52fce9d25 0x1c39f00381c03804 0x002cc08765c60c0c

def z1132 : W := mkw 0x0180000000000001 0xc00a9a5ad0000000 0xffffff800ff9ff3f 0xf57ffffffe078f1f

def z1133 : W := mkw 0xe8431add320ae548 0x0d80040401796af2 0x0000007ff00600c0 0x0a80000001f870e0

def z1134 : W := mkw 0xe4ca108c904ec9d9 0xcd02125c91204afa 0xe3c600000001fffc 0x61c0007898000fff

def z1135 : W := mkw 0x11a0000000000003 0xe03f9bfbd0000000 0xffc6000000000003 0xe03f3fff98000000

def z1136 : W := mkw 0x33e0000000000003 0xed3ffbfbf8004090 0xfffe007c000600c3 0xeabffffff80070e0

def z1137 : W := mkw 0x12a0000000000002 0x203763e938000000 0xfffe000000000003 0xe03fe7fff8000000

def z1138 : W := mkw 0x2040021002000001 0xcd00141080116090 0xe3c60ffc7e3fc7fb 0xffd33f789a39f3f3

def z1139 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc3ffffff1f9ffc7 0x79ffe0ff7fff8fef

def z1140 : W := mkw 0x0000210000010002 0x103000a006000500 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z1141 : W := mkw 0x13b4840008901221 0xe00ffb5bf8028005 0xfffe00000ff8003d 0xa44fff1ff807801f

def z1142 : W := mkw 0x0001ce724f200000 0x1208ed0006dfb000 0x0001fffffffe0003 0x9e13ff0007fff000

def z1143 : W := mkw 0xe042129c120ac148 0x0d00040401316af2 0x0001fffffe3ffff8 0x1fc0000007f9fff3

def z1144 : W := mkw 0x00014a7247200002 0x123d8d0006dd3000 0x0001f07ff0060001 0x0a2f1f0005f87000

def z1145 : W := mkw 0x35e8402084440891 0xed0f9b5bd0845098 0xfc00000000060001 0x020f1f1f00007000

def z1146 : W := mkw 0xc801bdcd2801e402 0x10b700ed076a8f60 0xfc01fffffff9ffc3 0x5dbf00ff07ff8fe0

def z1147 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff00038c3 0x18bf009f07f80ce0

def z1148 : W := mkw 0x1221ce724f200002 0x323deda12edfb000 0x0001fffffffe0003 0x9e3fff0007fff000

def z1149 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001f07ff1c60003 0x8a3fff0005fe7000

def z1150 : W := mkw 0x13b4840008901223 0xe03ffbfbf8028005 0xfffe000001c00007 0xe03ffffff806000c

def z1151 : W := mkw 0x31e0000000000001 0xed0f9b5bd0004090 0xfc00007c000600c1 0x0a8f1f1f000070e0

def z1152 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c60ffc703fc7f9 0x6bd33f789a39f3f3

def z1153 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe0ffc70000003 0xf83ffffffa380000

def z1154 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001ff83fffe0000 0x863fff0007fff000

def z1155 : W := mkw 0x0015ef724fb11222 0x123ded0006dfb505 0x03c7ffffffffff3f 0xff7fff609fffff1f

def z1156 : W := mkw 0x60c20294120a4148 0x0d020648103162d2 0x00060ffc7e3fc7fb 0xbfd33f601a39f3f3

def z1157 : W := mkw 0x13a0000000000001 0xe00212fbf8000000 0xfffe000000000001 0x60031ffff8000000

def z1158 : W := mkw 0x12a0000000000002 0x203763e938000000 0xfc06000000000000 0x601327ff18000000

def z1159 : W := mkw 0xca0139cd2001e402 0x10b700ed2f680f60 0xfffffffff001ffc3 0x79bf00fffff80fe0

def z1160 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffff00001c1ff3f 0xe17ffffffc060f1f

def z1161 : W := mkw 0x13a0000000000001 0xe00f9bfbf8000000 0xfc06000000000001 0x200f1f7f18000000

def z1162 : W := mkw 0x13b4840008901223 0xe03ffbfbf8028005 0xfffff0000ff9f83f 0xf57ffffffc078c1f

def z1163 : W := mkw 0x11a0000000000003 0xe03ffb5bd0000000 0xfff8000000000003 0xc03fff9fe0000000

def z1164 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f07f81c7f8fd 0x4bacd89fe5c67cfc

def z1165 : W := mkw 0x0000000000000002 0x003700e900000000 0xfc00000000000003 0xc03f3fff00000000

def z1166 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc00007ff001c7c1 0x498f007f01f803e0

def z1167 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc000ffff001c7c3 0x599f007f03f803e0

def z1168 : W := mkw 0x0215ad4249b11222 0x123561a02e4a8505 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z1169 : W := mkw 0x13a0000000000001 0xe00a9afbf8000000 0xfffe000000000003 0xe03ffffff8000000

def z1170 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x00000ffffffe0001 0x8e1fff0003fff000

def z1171 : W := mkw 0x13a0000000000003 0xe03dfbb3f8000000 0x1ffe000000000002 0xe03cffe7f8000000

def z1172 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc07fffffff9ffff 0x7dff20ff1fff8fff

def z1173 : W := mkw 0xedca318db04fedd9 0xcd8212ffd1204ffa 0xfffe00000001fffc 0x61c000fff8000fff

def z1174 : W := mkw 0x0100000000000003 0xc03ff9fbc0000000 0xfff8000000000003 0xc03fffffe0000000

def z1175 : W := mkw 0x0380000000000003 0xc03afafaf8000000 0xfffe000000000003 0xe03ffffff8000000

def z1176 : W := mkw 0x00014a7247200000 0x020ded0000dd3000 0x0000007ff0060001 0x8a0fff0001f87000

def z1177 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xffffff8001f83f07 0xe07ffffffe078f0f

def z1178 : W := mkw 0x0000423006000000 0x0000040000953000 0x0001fffffffe0003 0x9e133f0007fff000

def z1179 : W := mkw 0x0001ce724f200000 0x020ded0000dfb000 0x0000007ff03e0001 0x0a0f3f0001f9f000

def z1180 : W := mkw 0xe0c2108c100ac149 0xcd02125c91204af2 0xffc600000001fff8 0x61c000ff98000ff3

def z1181 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3fe0ffc7fffc7ff 0xffd3ff78fa3ff3ff

def z1182 : W := mkw 0x0214a50008911220 0x100060002e028505 0x03ffff800ff9ff3e 0xf550e060fe078f1f

def z1183 : W := mkw 0xfbe2318d300be549 0xed8212fff9204ff2 0xfffe00000001fff8 0x61c000fff8000ff3

def z1184 : W := mkw 0x0080000000000003 0xc03ffbf990000000 0xffc6000000000003 0xe03fffff98000000

def z1185 : W := mkw 0x59a129c520016403 0xf0bf9bfbd6680740 0xfc000f8070000701 0x001f1f7f02380300

def z1186 : W := mkw 0x53a0008400004003 0xe03ffbfbf8200240 0xfffe007c700000c3 0xe8bffffff83800e0

def z1187 : W := mkw 0x0314a50008911223 0xd03df9b2ee028505 0xffffff800ff9ff3f 0xf57ffffffe078f1f

def z1188 : W := mkw 0x0215ad4008911222 0x103560a02e4a8505 0x03ffff838ff9ff3e 0xf57ce0e0ffc78f1f

def z1189 : W := mkw 0x0214a50008911222 0x103060a02e028505 0xe3fffffc0ff9ffff 0xfdf0e0f8fe078fff

def z1190 : W := mkw 0x13a0000000000001 0xe00ffb5bf8000000 0xfc38000000000001 0x000fdf1f60000000

def z1191 : W := mkw 0xc80118cd2000e402 0x10b700ed07680a60 0xfc01fffff00000c3 0x58bf00ff07f800e0

def z1192 : W := mkw 0xc8019ccd2800e402 0x10b7604d076a8a60 0xfc01fffffff800c3 0x9cbfe01f07ff80e0

def z1193 : W := mkw 0x00010a5002000000 0x0005040000592000 0x00000ffffe3e0003 0x9e1f3f0003f9f000

def z1194 : W := mkw 0x13b4000000901223 0xe03ffbfbf8000005 0xfffe00000000003f 0xe07ffffff800001f

def z1195 : W := mkw 0xa8c33b59320ba54b 0xddb516b597596db2 0x1fc7f0038e3e3838 0xa66c3f879dc1fc13

def z1196 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03f9fffffffe0003 0xde3fff80e7fff000

def z1197 : W := mkw 0xa448502884448890 0x0d000004018458b8 0xfff9f07f8fc7f8ff 0xdfacc09fe5c67cfc

def z1198 : W := mkw 0xffe8318da045ec91 0xed8212fff9204ff8 0xfffe00000001fffc 0x618000fff8000ffc

def z1199 : W := mkw 0x51a0008400004001 0xe00f9b5bd0200240 0xfc00007c700000c1 0x088f1f1f003800e0

def z1200 : W := mkw 0x0215ce724fb01222 0x123deda02edfb005 0x03fffffffffe003f 0xfe7fffe0fffff01f

def z1201 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffffffe0001 0x1e2fdf0007fff000

def z1202 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffff0000fc1f83f 0xf53ffffffc060c1c

def z1203 : W := mkw 0x73e20084100a414b 0xed3ffbfbf82042d2 0xfffe007c0e07c7fb 0xfffffffff80073f3

def z1204 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff0003fc1 0x08bf00ff07f80fe0

def z1205 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc39fffff1c1ffc7 0x59bfc0ff67fe0fec

def z1206 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xffc6000000000001 0x600f1f7f98000000

def z1207 : W := mkw 0xa449de7acf648892 0x1f30640407dff8b8 0x03f9fffffffff8fe 0xdfb0e080e7fffcfc

def z1208 : W := mkw 0x00014a7247200000 0x120d8d0006dd3000 0x0001fffff0060001 0x1a0f1f0007f87000

def z1209 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03ffff800ff83f3c 0xa470e0e0fe078f1f

def z1210 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x03c60ffffe3fc73b 0xff5f3f609bf9f313

def z1211 : W := mkw 0x0001ce724f200000 0x120d8d0006dfb000 0x0001fffffffe0003 0x9e2fdf0007fff000

def z1212 : W := mkw 0x73f62184109b536b 0xed3ffbfbf82047d7 0xfffe00000001ffff 0xe1fffffff8000fff

def z1213 : W := mkw 0xc801bdcd2801e402 0x10b760ed076a8f60 0xfc01fffff039ffc3 0x59bf20ff07f98fe0

def z1214 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xffffff800ff83807 0xf43ffffffe078c0c

def z1215 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfc06000000000003 0x603f3fff18000000

def z1216 : W := mkw 0x13a1cc624d200003 0xf23ffbfbfece9000 0xfffffffff1c00003 0xf83ffffffffe0000

def z1217 : W := mkw 0x0101ce724f200001 0xd2089c12c6dfb000 0xfff9fffffffe0003 0xde2cd89fe7fff000

def z1218 : W := mkw 0x12a0000000000002 0x203763e938000000 0xfc06000000000001 0x201f277f18000000

def z1219 : W := mkw 0x00012b5002010002 0x103504a006592500 0x03c7fffffe3fff3b 0xff7f3fe09ff9ff13

def z1220 : W := mkw 0x13b4210000911223 0xe03ffbfbf8000505 0xfffe000000000703 0xe07ffffff8000303

def z1221 : W := mkw 0x00014a7247200002 0x023ded0000dd3000 0x0000007ff0060001 0x0a2fdf0001f87000

def z1222 : W := mkw 0xca1539cd2091f622 0x10b700ed2f680f65 0xfc39fffff001ffc7 0x59bf00ff67f80fec

def z1223 : W := mkw 0x37e8402084440893 0xed3ffbfbf8845098 0xfffe000000060003 0xe23ffffff8007000

def z1224 : W := mkw 0xe44a52bc964ec9d8 0x0d00040401b57afa 0x0001f07fffc7f8fc 0x1f80000005fe7cfc

def z1225 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfffff07f8fc7ffff 0xffecd8fffdc67fff

def z1226 : W := mkw 0xc80118cd2000e402 0x00b700ed01680a60 0xfc00007ff00000c1 0x08af009f01f800e0

def z1227 : W := mkw 0x00010a5002000000 0x0005040000592000 0x0000007ff0060001 0x0a0f1f0001f87000

def z1228 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x00000ffffe3e0003 0x9e1f3f0003f9f000

def z1229 : W := mkw 0x33f4a50008911223 0xfd3ffbfbfe02c595 0xfffffffc0fffffff 0xfffffffffe07ffff

def z1230 : W := mkw 0xc000108c0000c000 0x0002004c01200a60 0xfc01f07ff001f8c3 0x59af009f05f80ce0

def z1231 : W := mkw 0x11214a7247200000 0x220d8d0340dd3000 0x1c00007ff0060001 0x0a0f1f0701f87000

def z1232 : W := mkw 0x13b4a50008911222 0x303febeb7e028505 0x1c3fff8001f83f04 0x207fe7e77e078f0f

def z1233 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe00000e01c03b 0xf53ffffff8000010

def z1234 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0000007ff0060003 0x8a2fdf0001f87000

def z1235 : W := mkw 0x12b4a50008911222 0x303763e93e028505 0xffffff800ff9ff3f 0xf57fe7fffe078f1f

def z1236 : W := mkw 0x13a0000000000001 0xe00ffb5bf8000000 0xfffe000000000003 0xe01fff7ff8000000

def z1237 : W := mkw 0x12a0000000000002 0x203febe938000000 0xfc06000000000003 0xe03fffff18000000

def z1238 : W := mkw 0xe7de318c90dfdbf9 0xcd0212fef9204fff 0xfffe00000001fffc 0x61c000fff8000fff

def z1239 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01ffffffc1ffff 0x5dbf00ff07fe0ffc

def z1240 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000001 0x602fdffff8000000

def z1241 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc39fffffff9ffff 0x5dffc0ff67ff8fff

def z1242 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc01f07ff001f8c1 0x198f001f05f80ce0

def z1243 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe0f800e380003 0xf43ffffffa018000

def z1244 : W := mkw 0x13a0210000010003 0xf03ffbfbfe000500 0xfffe0f8000000703 0xe03ffffffa000300

def z1245 : W := mkw 0x0801ef736f212402 0x12bdeda106dfb500 0x0001fffffffe0003 0x9e3fff0007fff000

def z1246 : W := mkw 0x254a4230964e09d9 0xcd089c12c095709a 0x03f800000ffe003c 0x8640d800e007f01f

def z1247 : W := mkw 0xc80139cd2001e400 0x008700ed01680f60 0xfc000ffff001ffc3 0x599f00ff03f80fe0

def z1248 : W := mkw 0x13a0210000010003 0xf03ffbfbfe000500 0xffffff800e39ff3b 0xf57ffffffe018f13

def z1249 : W := mkw 0x0000000000000002 0x003de90000000000 0xfc00000000000003 0xc03fff9f00000000

def z1250 : W := mkw 0xe8c2108d300ae549 0xcd82125d91204af2 0xffc600000001c7f8 0x61c0007f980003f3

def z1251 : W := mkw 0x5ba108c520006403 0xe0bffbfbf8680240 0xfffe000070000003 0xe03ffffff8380000

def z1252 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xffc60ffc7e3fc7fb 0xffff3fff9a39f3f3

def z1253 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03ffff800ff9ff3c 0x7560c0e0fe078f1f

def z1254 : W := mkw 0x0214a50008911220 0x100060a02e028505 0x03ffff800ff9ff3c 0xf540e0e0fe078f1f

def z1255 : W := mkw 0xc801bdcd2801e402 0x10b760ed076a8f60 0xffc7fffffff9fffb 0xfdffe0ff9fff8ff3

def z1256 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc000ffff00000c3 0x189f001f03f800e0

def z1257 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fe0f800ff9ff3c 0xe550e0e0fa078f1f

def z1258 : W := mkw 0x25ca4230964e09d9 0xcd089e12d095709a 0x03c600000e3e0038 0xa6403f009801f013

def z1259 : W := mkw 0xc80139cd2001e400 0x1087004d07680f60 0xfc000ffff00007c1 0x088f001f03f803e0

def z1260 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3fe0ffc7e3fffff 0xffd33ff8fa39ffff

def z1261 : W := mkw 0x0215ad4008911222 0x103060a02e4a8505 0x03fffffffff9ff3e 0xfd70e0e0ffff8f1f

def z1262 : W := mkw 0xe8433bdd320be54a 0x1db004a407796ff2 0x03c7fffffe3ffffa 0xfff020e09ff9fff3

def z1263 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffff1c60003 0x1a3fdf0007fe7000

def z1264 : W := mkw 0x0394a50008911223 0xd03afafafe028505 0xffffff800ff9ff3f 0xf57ffffffe078f1f

def z1265 : W := mkw 0xca1539cd2091f622 0x10b700ed2f680f65 0xfffffffffe39ffff 0xfdff20fffff98fff

def z1266 : W := mkw 0x13a0000000000001 0xe00afbfbf8000000 0xfffe000000000003 0xe013fffff8000000

def z1267 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000000 0x603fe7fff8000000

def z1268 : W := mkw 0xc80139cd2001e402 0x10b5000407680f60 0xfc01fffff001ffc3 0x59bf009f07f80fe0

def z1269 : W := mkw 0x11a0000000000001 0xe007135bd0000000 0xfc00000000000000 0x0003071f00000000

def z1270 : W := mkw 0x00014a7247200002 0x023ded0000dd3000 0x00000ffffe3e0003 0x9e3fff0003f9f000

def z1271 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001f07fffc60003 0x9e2fdf0005fe7000

def z1272 : W := mkw 0x11a0000000000001 0xe00d9b13d0000000 0x1c00000000000000 0x000c1f0700000000

def z1273 : W := mkw 0x13a0840008000003 0xf03ffbfbfe028000 0xffffff800ff9f83f 0xf53ffffffe078c1c

def z1274 : W := mkw 0xc80139cd2001e400 0x108700ed07680f60 0xfc01fffff001ffc1 0x598f00ff07f80fe0

def z1275 : W := mkw 0x0000000000000002 0x003fe94900000000 0xfc00000000000003 0x803fff1f00000000

def z1276 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c7fffffe3fc7fb 0xffff3f789ff9f3f3

def z1277 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc39f07f8fc7f8fd 0x1facd89f65c67cfc

def z1278 : W := mkw 0x11a0210000010003 0xf03f9bfbd6000500 0xfc01ff800001ff03 0x513f1fff06000f00

def z1279 : W := mkw 0x13a0000000000001 0xe008fb12f8000000 0xfffe000000000001 0xa00cff1ff8000000

def z1280 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfc38000000000001 0x002fdf9f60000000

def z1281 : W := mkw 0xa4495a7ac7648890 0x0f00040401dd78b8 0x0001f07fffc7f8fc 0x1f80000005fe7cfc

def z1282 : W := mkw 0x11a0000000000001 0xe0089b12d0000000 0xfff8000000000003 0xc02cdf9fe0000000

def z1283 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe00000001c73b 0xe17ffffff8000313

def z1284 : W := mkw 0x00014a7247200002 0x123d8d0006dd3000 0x0001fffffe3e0003 0x9e3f3f0007f9f000

def z1285 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9ffffffc7f8ff 0xdfbfd89fe7fe7cfc

def z1286 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc00007ff001f8c1 0x498f009f01f80ce0

def z1287 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffff0000001f803 0xf13ffffffc000c00

def z1288 : W := mkw 0x0280000000000003 0xc03772f9b8000000 0xfffe000000000003 0xe03ffffff8000000

def z1289 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x003ffffffffe3f07 0xbe7fffe07fffff0f

def z1290 : W := mkw 0x13a0000000000003 0xe03ffb5bf8000000 0xfffe000000000003 0xa03fff1ff8000000

def z1291 : W := mkw 0xc80139cd2001e400 0x1087004d07680f60 0xfc01fffff001ffc3 0x59af009f07f80fe0

def z1292 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0039f07ff1c63805 0x0a2fdf8065fe7c0c

def z1293 : W := mkw 0x13b4210000911221 0xe00f9bfbf8000505 0xfffe00000001ff3d 0x614f1ffff8000f1f

def z1294 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe0f8000380703 0xe07ffffffa018303

def z1295 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff001ffc1 0x199f007f07f80fe0

def z1296 : W := mkw 0xb7e8502884448891 0xed08fb16f98458b8 0x03fff07f8fc7f8fc 0xbf80ff00fdc67cfc

def z1297 : W := mkw 0x0080000000000001 0xc007125990000000 0xffc6000000000003 0xe01f3f7f98000000

def z1298 : W := mkw 0x0215af500a911222 0x103564a02e5ba505 0x03ffffffffffff3f 0xff7fffe0ffffff1f

def z1299 : W := mkw 0x13a1cc624d200003 0xf23ffbfbfece9000 0xffffff838ff80003 0xf43fffffffc78000

def z1300 : W := mkw 0x13a0a50008010003 0xf03ffbfbfe028500 0xffffff800ff9ff03 0xf53ffffffe078f00

def z1301 : W := mkw 0xc815bdcd2891f620 0x1087004d076a8f65 0xfc01fffffff9fffd 0x1dcf001f07ff8fff

def z1302 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9ffff8fc7ffff 0xdfbcd8ffe7c67ffc

def z1303 : W := mkw 0x0100840008000003 0xd03df912c6028000 0xfff9ff800ff9f83f 0xd53fff9fe6078c1c

def z1304 : W := mkw 0x0001ce724f200000 0x1200040006dfb000 0x0001fffffffe0001 0x1e031f0007fff000

def z1305 : W := mkw 0x0215ef724fb11222 0x123064a02edfb505 0x03ffffffffffff3f 0xff73ffe0ffffff1f

def z1306 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffff001ffc3 0xd9bf3fff07f80fe0

def z1307 : W := mkw 0xc801bdcd2801e402 0x10b760ed076a8f60 0xfc01fffff1c1ffc3 0x59bfc0ff07fe0fe0

def z1308 : W := mkw 0x0215ce724fb01220 0x020ded0028dfb005 0x03fe007ffffe003d 0xae4fff00f9fff01f

def z1309 : W := mkw 0x13a0000000000001 0xe00f9bfbf8000000 0xfc38000000000001 0x000f1f9f60000000

def z1310 : W := mkw 0x0214a50008911220 0x000060a028028505 0x03fe0f800ff9ff3e 0xf550e0e0fa078f1f

def z1311 : W := mkw 0x0201ce724f200002 0x123deda02edfb000 0x0039fffffffe0003 0x9e3fff8067fff000

def z1312 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f07f8fc638fd 0x8eacd89fe5c67cfc

def z1313 : W := mkw 0x0001ef724f210002 0x123deda006dfb500 0x0001fffffffe3803 0x9e3fff8007fffc00

def z1314 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03c7fffffffe003b 0xbe7fff009ffff013

def z1315 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfff9fffff001ffc3 0xd9bfc0ffe7f80fe0

def z1316 : W := mkw 0xe8c2318d300be549 0xcd82125c91204ff2 0xe3c600000001fff8 0x61c0007898000ff3

def z1317 : W := mkw 0xc80139cd2001e402 0x10b7004d07680f60 0xfc01fffff001ffc3 0x19bf001f07f80fe0

def z1318 : W := mkw 0x0100000000000003 0xc03df912c0000000 0xfc00000000000003 0x803fff1f00000000

def z1319 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c7fffc7e3ffffb 0xfff33ff89e39fff3

def z1320 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x00000ffff03e0001 0x0a1f3f0003f9f000

def z1321 : W := mkw 0x5ba129c520016403 0xf0bffbfbfe680740 0xfffe0ffc7001c7c3 0xf9bffffffa3803e0

def z1322 : W := mkw 0x37fce5208cd51ab3 0xfd3ffbfbfe86d59d 0xffffff800fffff3f 0xf77ffffffe07ff1f

def z1323 : W := mkw 0xc80139cd2001e400 0x1087004d07680f60 0xfc01f07ff00038c1 0x088f001f05f80ce0

def z1324 : W := mkw 0x00014a7247200002 0x123d8d0006dd3000 0x00000ffff0060001 0x0a1f1f0003f87000

def z1325 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c7fffc7fffc7fb 0xfff3ff789e3ff3f3

def z1326 : W := mkw 0xc815bdcd2891f622 0x10b760ed076a8f65 0xfc01fffffff9ffff 0xddffe0ff07ff8fff

def z1327 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfc060f8000380701 0x205f3f7f1a018303

def z1328 : W := mkw 0x00014a7247200000 0x0200040000dd3000 0x0000007ff0060001 0x0a031f0001f87000

def z1329 : W := mkw 0x25484232c7640891 0xcf089d12c0957098 0x0000000000060000 0x02001f0000007000

def z1330 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfffe000000000003 0xe03ffffff8000000

def z1331 : W := mkw 0xe65ef7bc9edfdbfa 0x1d3064a42fb7ffff 0x03fffffffffffffe 0xfff0e0e0ffffffff

def z1332 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z1333 : W := mkw 0x13a0000000000003 0xe03dfb12f8000000 0xfffe000000000003 0xe03fff9ff8000000

def z1334 : W := mkw 0x0014a50008911220 0x1000000006028505 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z1335 : W := mkw 0x13b4210000911223 0xe03ffbfbf8000505 0xfffe000000003807 0xe03ffffff8000c0c

def z1336 : W := mkw 0x13a0000000000003 0xe03dfbb3f8000000 0x1ffe000000000003 0xa03fff87f8000000

def z1337 : W := mkw 0x11a0000000000003 0xe03ffb5bd0000000 0xfc00000000000001 0x001f3f1f00000000

def z1338 : W := mkw 0xead6318d309bf769 0xcd8212fdb9204ff7 0xfffe00000001fffc 0x61c000fff8000fff

def z1339 : W := mkw 0xe8c2318d300be54b 0xddb212fd97204ff2 0xffc7ff800e39fffa 0xf5f020ff9e018ff3

def z1340 : W := mkw 0x1321ce724f200002 0x323deda36edfb000 0x1c39fffffffe0000 0x1e2cc08767fff000

def z1341 : W := mkw 0x0000423006000000 0x00088c0000953000 0x00000ffffe3e0003 0x9e1f3f0003f9f000

def z1342 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xffc7fffff001ffc3 0xf9bf20ff9ff80fe0

def z1343 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc00007ff00000c3 0x489f007f01f800e0

def z1344 : W := mkw 0xd8a118cd2000e400 0x2087034d11680a60 0xfc00007ff00000c1 0x088f071f01f800e0

def z1345 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x03c7ffffffffc73b 0xff7fff609ffff313

def z1346 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfffffffff039ffc3 0xf9ffe0fffff98fe3

def z1347 : W := mkw 0x13a0402004000003 0xe03ffbfbf8841000 0xfffe00000fc60003 0xe63ffffff8067000

def z1348 : W := mkw 0xc815bdcd2891f620 0x10800004076a8f65 0xfff9fffffff9ffff 0xddecc09fe7ff8fff

def z1349 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfc39f07f81c7f8c7 0x5bacd89f65c67cec

def z1350 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfc39f07ff1c038c5 0x08afc09f65fe0cec

def z1351 : W := mkw 0x11a1486245200001 0xe20f9b5bd0cc1000 0xfc00000380000001 0x000f1f1f01c00000

def z1352 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c60ffc703e07c3 0xead33f789a39f3e3

def z1353 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfc00000000000003 0x802fdf1f00000000

def z1354 : W := mkw 0x1121ce724f200002 0x323ded0346dfb000 0x1c01fffffffe0003 0x9e3fff0707fff000

def z1355 : W := mkw 0xe44a52bc964ec9d8 0x0d00040401b57afa 0x03fffffffffffffe 0xfff0e0e0ffffffff

def z1356 : W := mkw 0x0180000000000001 0xc00a9a5ad0000000 0xffc6000000000003 0xe01f3f7f98000000

def z1357 : W := mkw 0x13a0000000000001 0xe00f9bfbf8000000 0xfffe000000000003 0xe01f3ffff8000000

def z1358 : W := mkw 0x0015ef724fb11220 0x1200040006dfb505 0x03c7ffffffffff3f 0xff533f609fffff1f

def z1359 : W := mkw 0x5ba129c520016403 0xf0bffbfbfe680740 0xfffffffff0000703 0xf83ffffffff80300

def z1360 : W := mkw 0x8000100800008000 0x0000000401000820 0xfc01fffff001f8c3 0x59bf009f07f80ce0

def z1361 : W := mkw 0x13a0000000000002 0x203deba378000000 0x1c3e000000000000 0x202ce78778000000

def z1362 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f07f8fc7f8fc 0x5facc09fe5c67cfc

def z1363 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xfff8000000000001 0x400f1f9fe0000000

def z1364 : W := mkw 0x33e0000000000003 0xed3ffbfbf8004090 0xfffe0ffc0e3fc7fb 0xfffffffffa01f3f3

def z1365 : W := mkw 0x33e2c6325f2a0149 0xef08ff12f897f092 0x03fe00000ffe0038 0xa640ff00f807f013

def z1366 : W := mkw 0x0080000000000003 0xc03712f990000000 0xfc00000000000003 0x403f1fff00000000

def z1367 : W := mkw 0xc80118cd2000e402 0x10b7004d07680a60 0xfc01fffff001c7c3 0x59bf007f07f803e0

def z1368 : W := mkw 0xc801bdcd2801e402 0x10b760ed076a8f60 0xfff9fffffff9ffff 0xddbfe0ffe7ff8ffc

def z1369 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfffff07f8ffff8ff 0xffecf89ffdc7fcff

def z1370 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe000000000001 0xa01fff7ff8000000

def z1371 : W := mkw 0x59a108c520006401 0xe08f9b5bd0680240 0xfc00000070000001 0x000f1f1f00380000

def z1372 : W := mkw 0x2548423086440891 0xcd089c12c0957098 0x03f800000ffe003c 0x8600ff00e007f01c

def z1373 : W := mkw 0x11a0402004000001 0xe00f9b5bd0841000 0xfc01f07f8fc60003 0x9e2fdf1f05c67000

def z1374 : W := mkw 0x11a0000000000003 0xe03f9bfbd0000000 0xfff8000000000003 0xc03fdfffe0000000

def z1375 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0001f07ff1c60001 0x0a2fdf0005fe7000

def z1376 : W := mkw 0x0080000000000002 0x003702e910000000 0xfc06000000000003 0x603f27ff18000000

def z1377 : W := mkw 0x0100000000000002 0x003de90240000000 0x1c38000000000003 0x803fff8760000000

def z1378 : W := mkw 0x0001ce724f200002 0x123deda006dfb000 0x0001fffffffe0003 0xde3fffe007fff000

def z1379 : W := mkw 0x0001ce724f200000 0x020ded0000dfb000 0x0001f07ffffe0003 0x9e2fff0005fff000

def z1380 : W := mkw 0xc80139cd2001e402 0x10b761ed07680f60 0xfc01fffff001ffc3 0x59bf27ff07f80fe0

def z1381 : W := mkw 0xca1539cd2091f622 0x10b700ed2f680f65 0xffffffffffc1ffff 0xfdffc0fffffe0fff

def z1382 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3fe0ffc7e3fc7fb 0xfff3fff8fa39f3f3

def z1383 : W := mkw 0xe7deb58c98dfdbfb 0xdd3272feff22cfff 0xffffff800ff9fffe 0xf5f0e0fffe078fff

def z1384 : W := mkw 0x0015ef724fb11220 0x120d8d0006dfb505 0x0001ffffffffff3d 0x1f4f1f0007ffff1f

def z1385 : W := mkw 0x11a1084000000001 0xe00f9b5bd0480000 0xfc00007ff0000001 0x080f1f1f01f80000

def z1386 : W := mkw 0x53b4a58408915223 0xf03ffbfbfe228745 0xfffffffc7ff9ffff 0xfdfffffffe3f8fff

def z1387 : W := mkw 0x13b4840008901223 0xe03ffbfbf8028005 0xfffe0f800ff9c73f 0xf57ffffffa07831f

def z1388 : W := mkw 0x8215bd4808919222 0x103560a42f4a8d25 0xfffffffffff9ffff 0xfdffe0ffffff8fff

def z1389 : W := mkw 0xf5ea52bc964ec9d9 0xed0f9f5fd1b57afa 0xfc00007ff00600c1 0x0a8f1f1f01f870e0

def z1390 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x03fffffffffe383f 0xbe7fff80fffffc1f

def z1391 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xffffff8001c1ff07 0xf13ffffffe060f0c

def z1392 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9f07f81c638c7 0xcaacd89fe5c67cec

def z1393 : W := mkw 0xe5ca108c904ec9d9 0xcd02125ed1204afa 0xffc600000001c7f8 0x61c0007f980003f3

def z1394 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xffc7fffffe39fffb 0xfdff20ff9ff98ff3

def z1395 : W := mkw 0x1320000000000002 0x203de9a368000000 0x1c38000000000000 0x802cff8760000000

def z1396 : W := mkw 0xe44bdefedf6ec9d8 0x1f00040407fffafa 0x0001fffffffffffc 0x1fc0000007ffffff

def z1397 : W := mkw 0x02014a7247200002 0x023deda028dd3000 0x03fe007ff0060003 0xea3fffe0f9f87000

def z1398 : W := mkw 0x13b4210000911221 0xe00212fbf8000505 0xfffe0f800e39ff3f 0xf5533ffffa018f1f

def z1399 : W := mkw 0x275ce732cff51ab3 0xdf38fdb2ee97f59d 0x03ffff800fffff3e 0xf770ffe0fe07ff1f

def z1400 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03fff0000ff9ff3c 0xe560e0e0fc078f1f

def z1401 : W := mkw 0xdaa139cd2001e402 0x30b763ed3f680f60 0xfffffffff001ffc3 0xf9bfe7fffff80fe0

def z1402 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x0001fffffffe0003 0x9e3fff0007fff000

def z1403 : W := mkw 0x0000423006000000 0x00088c0000953000 0x0001f07fffc60003 0x9e2fdf0005fe7000

def z1404 : W := mkw 0xc000318c0001c002 0x103200ec07200f60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z1405 : W := mkw 0xa448502884448892 0x0d3de904018458b8 0x0001f07f8fc7f8ff 0x9fbfff0005c67cfc

def z1406 : W := mkw 0xc80118cd2000e400 0x1087004d07680a60 0xfc01fffff00000c1 0x188f001f07f800e0

def z1407 : W := mkw 0x0001ce724f200002 0x023ded0000dfb000 0x0000007ffffe0003 0x8e3fff0001fff000

def z1408 : W := mkw 0x1234a50008911222 0x303561a12e028505 0x03ffff800ff9ff3e 0xf570e0e0fe078f1f

def z1409 : W := mkw 0xc801bfdf6b21e400 0x12800404077baf60 0x0001fffff039ffc0 0x1980000007f98fe0

def z1410 : W := mkw 0xedcb5afdb64eedd9 0xcd8f9e5fd1fd7afa 0xfc00007ff00600c1 0x0a8f1f1f01f870e0

def z1411 : W := mkw 0x0294a50008911223 0xd03772f9be028505 0xffffff800ff9ff3f 0xf57ffffffe078f1f

def z1412 : W := mkw 0xc801bdcf6921e402 0x12b761ed076a8f60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z1413 : W := mkw 0xc815bdcd2891f622 0x10b700ed076a8f65 0xfc01fffff039ffc3 0x59ff00ff07f98fe3

def z1414 : W := mkw 0x13a0000000000003 0xe03dfbb3f8000000 0xfffe000000000003 0xe02cff9ff8000000

def z1415 : W := mkw 0x0080210000010003 0xd03712f996000500 0xffc7ff800e39ff3b 0xf57f3fff9e018f13

def z1416 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0xe3c60ffc7e3e07f9 0xaed33f789a39f3f3

def z1417 : W := mkw 0xe5ca108c904ec9d9 0xcd02125ed1204afa 0xffffff800ff9fffe 0xf5f0e0fffe078fff

def z1418 : W := mkw 0x0201ce724f200002 0x123deda02edfb000 0x03ffffffffffc73b 0xff7fffe0fffff313

def z1419 : W := mkw 0x0001ef724f210002 0x123deda006dfb500 0x03c7ffffffffff3b 0xff7fffe09fffff13

def z1420 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc01fffffe07ffc3 0xdfbf18ff07f87fe0

def z1421 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x03f9fffffffe003f 0x9e3fff00e7fff01c

def z1422 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe00000001f83f 0xe13ffffff8000c1c

def z1423 : W := mkw 0x13a1084000000003 0xf03ffbfbfe480000 0xfffff00380000003 0xe03ffffffdc00000

def z1424 : W := mkw 0x0001ce724f200000 0x020ded0000dfb000 0x0000007ff1c60001 0x0a0fdf0001fe7000

def z1425 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0xe001ffffffffc0c3 0xdfbfff1807fff0e0

def z1426 : W := mkw 0x10a0000000000002 0x203703e910000000 0xfc00000000000003 0x403f07ff00000000

def z1427 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffe0f800001c703 0xf13ffffffa000300

def z1428 : W := mkw 0x73e20084100a414b 0xed3ffbfbf82042d2 0xfffe0ffc7001c7fb 0xf9fffffffa3803f3

def z1429 : W := mkw 0xa448d63acf648890 0x0f0004040197f8b8 0x0001f07f8ffff8fc 0x1f80000005c7fcfc

def z1430 : W := mkw 0xdaa139cd2001e402 0x30b763ed3f680f60 0x0007fffff001ffc0 0x399327601ff80fe0

def z1431 : W := mkw 0xa4495a7ac7648890 0x0f00040401dd78b8 0x0000007ff00600c0 0x0a80000001f870e0

def z1432 : W := mkw 0x0001ce724f200000 0x120d8d0006dfb000 0x0001f07ff1c60001 0x0a0f1f0005fe7000

def z1433 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc000ffff00007c1 0x089f007f03f803e0

def z1434 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xffc7fffff001fffb 0x79ff00ff9ff80ff3

def z1435 : W := mkw 0x13b4210000911223 0xf03ffbfbfe000505 0xffffff800001ff3f 0xf17ffffffe000f1f

def z1436 : W := mkw 0x00014a7247200002 0x123d8d0006dd3000 0x0001ffffffc60003 0x9e3fdf0007fe7000

def z1437 : W := mkw 0xda2139cd2001e402 0x30b761ed2f680f60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z1438 : W := mkw 0xe5cb5afed76ec9d9 0xcf0f9f5ed1fd7afa 0xfc00007ff00600c1 0x0a8f1f1f01f870e0

def z1439 : W := mkw 0x13a0000000000001 0xe00ffb5bf8000000 0xfffe000000000003 0xe02fff9ff8000000

def z1440 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0000007ffe3e0001 0x8e0f3f0001f9f000

def z1441 : W := mkw 0x0215ce724fb01222 0x123ded002edfb005 0x0007fffffffe0003 0xbe7fff001ffff003

def z1442 : W := mkw 0x11a0000000000001 0xe00f9b5bd0000000 0xffc0000000000003 0xc00f1f1f80000000

def z1443 : W := mkw 0x33e0000000000003 0xed3ffbfbf8004090 0xfffe00000e06003b 0xe63ffffff8007010

def z1444 : W := mkw 0x00014a7247200000 0x020d8d0000dd3000 0x0001f07ff0060003 0x1a2f1f0005f87000

def z1445 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x00060ffff03e0701 0x2a5f3f601bf9f303

def z1446 : W := mkw 0x0100000000000001 0xc00d9912c0000000 0xfc00000000000001 0x000f1f1f00000000

def z1447 : W := mkw 0x13b4840008901223 0xe03ffbfbf8028005 0xfffe000000380003 0xe07ffffff8018003

def z1448 : W := mkw 0x13a0210000010003 0xe03ffbfbf8000500 0xfffe00000001ff03 0xe13ffffff8000f00

def z1449 : W := mkw 0x0214a50008911220 0x000060a028028505 0x03fff0000ff9ff3e 0xf560e0e0fc078f1f

def z1450 : W := mkw 0x0000a50008010002 0x103fe9e906028500 0xfc01ff800ff9ff03 0xd53fffff06078f00

def z1451 : W := mkw 0x0001486004000002 0x103de90006cc1000 0x0001ffffffc60003 0x9e3fff0007fe7000

def z1452 : W := mkw 0xd8a139cd2001e402 0x30b703ed17680f60 0xfc01fffff001ffc3 0x59bf07ff07f80fe0

def z1453 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0039fffffffe3807 0x9e3fff8067fffc0c

def z1454 : W := mkw 0x0214a50008911222 0x003060a028028505 0x03fe00000ff9ff3e 0xe570e0e0f8078f1f

def z1455 : W := mkw 0xca1539cd2091f622 0x10b760ed2f680f65 0xfffffffff001ffff 0xf9ffe0fffff80fff

def z1456 : W := mkw 0x13a0000000000001 0xe008fb12f8000000 0x1ffe000000000000 0xa02cff87f8000000

def z1457 : W := mkw 0xa548502884448891 0xcd089816c18458b8 0xfff9ffff8ffff8ff 0xdfbcf89fe7c7fcfc

def z1458 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xfc000ffff001ffc1 0x499f00ff03f80fe0

def z1459 : W := mkw 0x0001ce724f200002 0x123deda106dfb000 0x1c01fffffffe0003 0x9e3fff8707fff000

def z1460 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfc39f00001c03805 0x002fdf9f64060c0c

def z1461 : W := mkw 0xc80139cd2001e402 0x10b700ed07680f60 0xffc1fffffe01fffb 0xddbf00ff87f80ff0

def z1462 : W := mkw 0x13214a7247200002 0x223deda368dd3000 0x1c38007ff0060001 0x0a2fdf8761f87000

def z1463 : W := mkw 0x0214a50008911222 0x103060a02e028505 0x03ffff8001f9ff3c 0x6170e0e0fe078f1f

def z1464 : W := mkw 0x13b4a50008911223 0xf03773fbfe028505 0xffffff800ff9ff3e 0xf573e7fffe078f1f

def z1465 : W := mkw 0xc80118cd2000e400 0x0087004d01680a60 0xfc01fffff001ffc3 0x59bf00ff07f80fe0

def z1466 : W := mkw 0x00014a7006000002 0x103d8c0006dd3000 0x0001fffffffe0003 0x9e3fff0007fff000

def z1467 : W := mkw 0x13b4a50008911223 0xf03dfbb3fe028505 0x1fffff800ff9ff3e 0xf57cffe7fe078f1f

def z1468 : W := mkw 0xc000108c0000c000 0x0000000401200a60 0xfc01fffff001ffc3 0x59ac009f07f80fe0

def z1469 : W := mkw 0x1120000000000002 0x203de90340000000 0x1c00000000000003 0x803fff0700000000

def z1470 : W := mkw 0x0001ce724f200000 0x020ded0000dfb000 0x00000ffffffe0003 0x9e1fff0003fff000

def z1471 : W := mkw 0xc80118cd2000e400 0x0080000401680a60 0xfc00007ff00000c1 0x088c001f01f800e0

def z1472 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x03fffffffffe3807 0xfe3fffe0fffffc0c

def z1473 : W := mkw 0x73e20294120a4149 0xed0216fbf83162d2 0xfffe0ffc7e3fc7f8 0x7fc000fffa39f3f3

def z1474 : W := mkw 0x37e8000080440893 0xed3ffbfbf8004098 0xfffe00000000003f 0xe03ffffff800001c

def z1475 : W := mkw 0x25ca4230964e09d9 0xcd089e12d095709a 0x03f800000fc6003c 0x8600df00e006701c

def z1476 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffffffe0001 0x1e1f3f0007fff000

def z1477 : W := mkw 0x12a0000000000002 0x203763e938000000 0x1c06000000000000 0x203f27e718000000

def z1478 : W := mkw 0x60c20294120a4149 0xcd021658903162d2 0x03c60ffc7e3fc7f8 0xbfd33f609a39f3f3

def z1479 : W := mkw 0x0214e7300e911222 0x1038eca02e97b505 0x03ffffffffffff3f 0xff7fffe0ffffff1f

def z1480 : W := mkw 0xc80139cd2001e400 0x008700ed01680f60 0xfc00007ff00007c1 0x088f007f01f803e0

def z1481 : W := mkw 0xc8015aff6720e400 0x0280040401fd3a60 0x0000007ff00600c0 0x0a80000001f870e0

def z1482 : W := mkw 0x0214a50008911222 0x103560a12e028505 0x1fffff800ff9ff3e 0xf57ce0e7fe078f1f

def z1483 : W := mkw 0x0001ce724f200002 0x123ded0006dfb000 0x0001fffffffe0000 0x9e13ff0007fff000

def z1484 : W := mkw 0x13a0c4200c000003 0xf03ffbfbfe869000 0xffffffff8ffe0003 0xfe3fffffffc7f000

def z1485 : W := mkw 0x13a0000000000003 0xe03ffbfbf8000000 0xfffff0000fc00003 0xf43ffffffc060000

def z1486 : W := mkw 0x0001ce724f200002 0x1235040006dfb000 0x0001fffffffe0003 0x9e3f3f0007fff000

def z1487 : W := mkw 0x0215ef724fb11222 0x123deda02edfb505 0x03fffffffffe0703 0xfe7fffe0fffff303

def z1488 : W := mkw 0x0001ce724f200000 0x120d8d0006dfb000 0x0001fffffffe0003 0x9e1f3f0007fff000

def z1489 : W := mkw 0x13b4a50008911223 0xf03ffbfbfe028505 0xfffe000000000003 0xe03ffffff8000000

def z1490 : W := mkw 0xa5ca5028944e89d9 0xcd089a16d18458ba 0xfffff07f8fc7f8ff 0xffecd89ffdc67cff

def z1491 : W := mkw 0x11a0000000000003 0xe03ffbfbd0000000 0xfc00000000000003 0xc03fffff00000000

def z1492 : W := mkw 0x37e8402084440893 0xed3ffbfbf8845098 0xfffff07f8fc6003f 0xfe3ffffffdc6701c

def z1493 : W := mkw 0xead6b58d389bf76b 0xddb272fdbf22cff7 0xffffff800ff9fffe 0xf5f0e0fffe078fff

def z1494 : W := mkw 0xca15bdcd2891f622 0x10b760ed2f6a8f65 0xfffffffff1c1ffc7 0xf9bfe0fffffe0fec

def z1495 : W := mkw 0x17a8402084440893 0xe03ffbfbf8841008 0xfffe000001c00007 0xe03ffffff806000c

def z1496 : W := mkw 0x0001ef724f210002 0x123deda006dfb500 0x03f9ffffffffff3f 0xdf3fffe0e7ffff1c

def z1497 : W := mkw 0x00014a7247200002 0x023ded0000dd3000 0x0000007ff0060001 0x0a1f3f0001f87000

def z1498 : W := mkw 0xc81539cd2091f622 0x10b700ed07680f65 0xfc01fffff001ffff 0x59ff00ff07f80fff

def z1499 : W := mkw 0xca15bdcd2891f622 0x10b700ed2f6a8f65 0xfffffffffff9ffff 0x7dff00ffffff8fff

def z1500 : W := mkw 0x13a0402004000003 0xe03ffbfbf8841000 0xfffff00381c00003 0xe03ffffffdc60000

def z1501 : W := mkw 0x11a0000000000000 0x200f8b4b50000000 0x1c00000000000000 0x000f070700000000

def z1502 : W := mkw 0xc8033bdd320be548 0x1080040407792f62 0x0001fffff039ffc0 0x19c0000007f98fe3

def z1503 : W := mkw 0xc80118cd2000e402 0x10b7004d07680a60 0xfc01fffff001f8c3 0x59bf009f07f80ce0

def z1504 : W := mkw 0x13a0000000000001 0xe00212fbf8000000 0xfffe000000000000 0xe0003ffff8000000

def z1505 : W := mkw 0x0215ce724fb01222 0x123ded002edfb005 0x03ffffffffffc73f 0xff7fff60fffff31f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z8,z4,z5]),(0,[z7,z9,z0,z2,z3,z4,z5]),(0,[z7,z10,z0,z2,z3,z4,z11]),(0,[z7,z0,z2,z3,z12,z4,z5])],[(0,[z13,z0,z1,z2,z3,z4,z5]),(0,[z14,z15,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z16,z3,z4,z5]),(0,[z17,z7,z0,z18,z3,z4,z5]),(0,[z7,z0,z2,z3,z19,z4,z5]),(0,[z7,z20,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z4,z5]),(0,[z7,z0,z21,z2,z3,z4,z5]),(0,[z7,z0,z22,z23,z3,z4,z5]),(0,[z7,z0,z2,z3,z24,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z26]),(0,[z7,z0,z2,z27,z3,z28,z4])],[(0,[z7,z0,z2,z29,z3,z4,z5]),(0,[z0,z1,z2,z3,z30,z4,z5]),(0,[z7,z0,z2,z31,z3,z4,z5]),(1,[z7,z0,z2,z32,z3,z4]),(0,[z7,z0,z33,z3,z4,z5,z34]),(0,[z7,z0,z22,z3,z28,z4,z5]),(1,[z7,z0,z2,z3,z4,z35]),(0,[z7,z0,z2,z3,z24,z4,z36]),(0,[z7,z0,z2,z3,z37,z4,z5])],[(0,[z7,z0,z2,z3,z4,z38,z5]),(0,[z7,z0,z39,z2,z3,z4,z5])],[(0,[z7,z0,z40,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z41,z4,z5]),(0,[z7,z0,z2,z3,z42,z4,z5]),(0,[z7,z0,z2,z43,z3,z4,z5])],[(0,[z14,z44,z0,z2,z3,z4,z5]),(0,[z7,z45,z0,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z24,z4,z5]),(0,[z46,z7,z0,z2,z3,z4,z5]),(0,[z47,z0,z2,z3,z48,z4,z5]),(0,[z7,z0,z2,z49,z3,z4,z5]),(0,[z7,z50,z0,z2,z3,z4,z35]),(0,[z7,z0,z2,z51,z3,z4,z5]),(0,[z7,z0,z2,z28,z4,z5,z52])],[(0,[z0,z1,z2,z53,z3,z4,z5]),(0,[z7,z0,z18,z2,z3,z4,z25]),(0,[z7,z0,z54,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z55,z5])]],
   [[(0,[z56,z17,z7,z0,z3,z4,z5]),(0,[z57,z7,z2,z3,z58,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z59]),(0,[z60,z61,z0,z2,z3,z4,z5]),(0,[z62,z7,z0,z2,z3,z4,z5])],[(0,[z63,z15,z0,z2,z3,z4,z5]),(0,[z7,z64,z0,z53,z3,z4,z5]),(0,[z57,z7,z0,z65,z3,z4,z5]),(0,[z66,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z67]),(0,[z7,z0,z2,z68,z69,z3,z4])],[(0,[z70,z7,z0,z2,z3,z4,z71]),(0,[z72,z7,z0,z2,z3,z4,z5]),(0,[z0,z2,z73,z3,z4,z74,z5]),(0,[z7,z0,z2,z3,z4,z74,z36]),(0,[z7,z0,z2,z3,z4,z36,z75]),(0,[z76,z0,z2,z3,z4,z5,z77]),(0,[z7,z78,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z79,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z80,z5]),(0,[z7,z64,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z81,z25]),(0,[z7,z0,z2,z3,z4,z25,z52]),(0,[z7,z0,z82,z2,z3,z4,z5]),(0,[z7,z0,z83,z2,z3,z4,z5]),(1,[z7,z0,z84,z3,z4,z5])],[(0,[z7,z0,z1,z2,z3,z4,z25]),(0,[z15,z0,z18,z2,z3,z4,z5]),(0,[z7,z50,z2,z3,z85,z4,z5]),(0,[z7,z0,z2,z3,z86,z4,z25]),(0,[z7,z0,z87,z2,z3,z4,z88]),(0,[z7,z0,z2,z89,z3,z4,z5])],[(0,[z7,z0,z2,z3,z90,z4,z5]),(0,[z7,z0,z73,z3,z91,z4,z5]),(0,[z7,z0,z2,z92,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z93,z25]),(0,[z7,z0,z33,z3,z94,z4,z5]),(1,[z95,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z96]),(0,[z7,z0,z2,z3,z86,z4,z36]),(0,[z7,z0,z2,z3,z97,z4,z5])],[(0,[z98,z7,z0,z2,z3,z4,z5]),(0,[z7,z99,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z100]),(0,[z101,z7,z0,z2,z3,z4,z5]),(0,[z7,z102,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z103]),(0,[z7,z0,z2,z104,z3,z4,z25]),(0,[z7,z0,z2,z68,z3,z4,z25])],[(0,[z7,z105,z0,z106,z3,z4,z5]),(0,[z7,z0,z2,z3,z107,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z108])]],
   [[(0,[z0,z1,z2,z3,z94,z4,z5]),(0,[z15,z64,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z81,z5]),(0,[z7,z109,z0,z2,z3,z4,z5]),(0,[z7,z10,z2,z33,z3,z4,z5]),(0,[z7,z0,z33,z33,z3,z4,z5]),(0,[z7,z0,z2,z69,z3,z4,z25]),(0,[z7,z0,z110,z111,z3,z4,z5]),(0,[z7,z0,z2,z68,z3,z4,z6])],[(0,[z15,z0,z1,z2,z3,z4,z5]),(0,[z0,z112,z1,z2,z3,z4,z5]),(0,[z113,z15,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z86,z4,z5]),(0,[z7,z0,z87,z53,z3,z4,z5]),(0,[z7,z0,z114,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z115,z5]),(0,[z7,z0,z2,z3,z116,z4,z5]),(1,[z117,z0,z2,z3,z4,z5]),(0,[z7,z118,z0,z2,z3,z4,z119]),(0,[z7,z0,z0,z22,z3,z4,z5]),(0,[z7,z0,z22,z87,z3,z4,z5]),(0,[z7,z0,z2,z69,z3,z4,z36]),(0,[z7,z0,z3,z86,z4,z120,z5]),(0,[z7,z121,z0,z2,z3,z4,z5])],[(0,[z102,z0,z1,z2,z3,z4,z5]),(0,[z7,z105,z0,z33,z3,z4,z5]),(0,[z7,z0,z18,z23,z3,z4,z5]),(0,[z7,z0,z122,z2,z3,z4,z5]),(0,[z123,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z110,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z124,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z33,z3,z4,z5]),(0,[z15,z0,z2,z68,z3,z4,z5]),(0,[z7,z10,z0,z2,z3,z4,z125]),(0,[z7,z0,z126,z2,z3,z4,z5]),(0,[z7,z0,z87,z2,z3,z4,z25]),(0,[z7,z0,z2,z110,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z5,z127]),(0,[z7,z0,z2,z24,z4,z5,z77]),(0,[z7,z0,z2,z128,z3,z4,z5])],[(0,[z129,z7,z0,z2,z3,z4,z5]),(0,[z130,z7,z0,z2,z3,z4,z36]),(1,[z7,z0,z122,z3,z4,z5]),(0,[z7,z61,z0,z131,z3,z4,z5]),(0,[z7,z0,z87,z2,z3,z4,z36]),(0,[z7,z0,z132,z2,z16,z4,z5]),(0,[z7,z0,z2,z133,z3,z4,z5]),(0,[z7,z0,z68,z134,z3,z4,z5])],[(0,[z7,z135,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z69,z3,z4,z5]),(0,[z98,z0,z2,z73,z3,z4,z5])],[(0,[z136,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z137,z5]),(0,[z138,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z139,z5]),(0,[z7,z0,z140,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z141,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z142]),(0,[z7,z0,z2,z3,z4,z5,z143]),(0,[z7,z0,z2,z27,z3,z4,z5]),(0,[z144,z7,z0,z2,z3,z4,z5])],[(0,[z145,z0,z1,z2,z3,z4,z5]),(0,[z15,z0,z2,z110,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z36,z52]),(1,[z7,z64,z0,z86,z4,z5]),(0,[z7,z0,z2,z3,z146,z4,z5]),(0,[z7,z0,z2,z147,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z148]),(0,[z15,z0,z87,z2,z3,z4,z5]),(0,[z7,z0,z2,z110,z149,z4,z5])],[(0,[z7,z105,z0,z2,z3,z4,z150]),(1,[z17,z0,z53,z3,z4,z5]),(1,[z7,z0,z151,z3,z4,z5]),(1,[z7,z0,z39,z3,z4,z5]),(0,[z7,z152,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z153,z3,z4,z5]),(0,[z7,z0,z2,z154,z3,z4,z5]),(1,[z7,z0,z155,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z77]),(0,[z7,z0,z2,z156,z3,z4,z52])],[(0,[z7,z0,z157,z2,z3,z4,z5]),(0,[z7,z0,z2,z33,z3,z4,z25]),(0,[z7,z0,z2,z3,z158,z4,z5]),(1,[z7,z0,z2,z3,z4,z159]),(0,[z7,z160,z0,z2,z3,z4,z5]),(0,[z161,z7,z0,z2,z3,z4,z5])],[(0,[z70,z7,z0,z33,z3,z4,z5]),(0,[z162,z7,z0,z132,z3,z4,z5]),(0,[z7,z0,z163,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z94,z4,z5]),(0,[z7,z0,z2,z3,z164,z4,z5]),(0,[z7,z0,z2,z58,z4,z5,z77]),(1,[z7,z0,z165,z3,z4,z5]),(1,[z7,z0,z2,z3,z4,z166]),(0,[z7,z0,z2,z3,z167,z4,z5]),(0,[z7,z0,z168,z2,z3,z4,z5]),(1,[z7,z102,z0,z3,z120,z5]),(0,[z7,z0,z2,z3,z4,z5,z169])],[(0,[z170,z15,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z171,z4,z115,z5]),(0,[z172,z10,z0,z2,z3,z4,z5]),(0,[z170,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z3,z173,z4,z5]),(0,[z7,z61,z2,z3,z4,z36,z5]),(0,[z7,z0,z2,z3,z174,z4,z5]),(1,[z7,z0,z2,z3,z4,z175]),(0,[z7,z0,z2,z176,z3,z4,z5]),(0,[z7,z0,z2,z3,z146,z4,z81])],[(0,[z70,z7,z1,z2,z3,z4,z5]),(1,[z7,z0,z2,z3,z4,z177]),(0,[z7,z0,z2,z3,z178,z4,z5]),(0,[z7,z0,z2,z179,z3,z4,z5]),(0,[z180,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z58,z4,z25]),(0,[z7,z0,z2,z3,z85,z4,z5]),(0,[z7,z0,z2,z181,z3,z4,z36]),(0,[z7,z0,z2,z182,z3,z4,z5]),(1,[z7,z0,z2,z3,z4,z124])],[(0,[z15,z0,z2,z3,z4,z183,z5]),(0,[z15,z0,z2,z33,z3,z4,z5]),(0,[z47,z0,z2,z53,z3,z4,z5]),(0,[z7,z0,z2,z184,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z185,z5]),(0,[z13,z7,z0,z2,z3,z4,z5]),(1,[z186,z0,z2,z3,z4,z5]),(0,[z7,z0,z155,z110,z3,z4,z5])],[(0,[z187,z7,z0,z2,z3,z4,z5]),(2,[z1,z2,z3,z4,z25]),(0,[z188,z15,z0,z2,z3,z4,z5]),(0,[z162,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z11,z5]),(0,[z7,z0,z22,z189,z3,z4,z5]),(0,[z188,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z190,z3,z4,z5]),(0,[z7,z0,z191,z2,z3,z4,z5]),(0,[z7,z0,z192,z2,z3,z4,z5])],[(0,[z7,z0,z193,z2,z3,z4,z5]),(0,[z194,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z195,z4,z25])],[(0,[z15,z0,z2,z3,z58,z4,z5]),(1,[z7,z105,z2,z3,z4,z25]),(0,[z196,z7,z0,z2,z3,z4,z5]),(0,[z197,z7,z0,z2,z3,z4,z25]),(0,[z7,z198,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z24,z85,z5]),(0,[z7,z0,z16,z3,z4,z81,z5]),(0,[z199,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z149,z3,z24,z5]),(0,[z7,z0,z2,z27,z156,z4,z5])],[(1,[z1,z2,z3,z4,z5,z25]),(0,[z7,z0,z2,z3,z4,z200,z5]),(0,[z7,z0,z16,z3,z86,z4,z5])],[(0,[z201,z7,z0,z2,z3,z4,z5]),(0,[z202,z0,z2,z73,z3,z4,z5]),(0,[z7,z0,z203,z33,z3,z4,z5]),(0,[z7,z0,z2,z204,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z25,z25]),(0,[z56,z7,z0,z2,z3,z4,z36]),(0,[z7,z205,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z206,z5]),(0,[z7,z0,z2,z3,z207,z4,z5]),(0,[z7,z0,z2,z3,z28,z4,z5])],[(0,[z7,z0,z2,z3,z208,z4,z5]),(0,[z7,z0,z209,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z146,z5,z6])],[(0,[z7,z0,z33,z3,z4,z36,z5]),(0,[z210,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z25,z6]),(0,[z7,z0,z155,z2,z3,z4,z5])]],
   [[(0,[z15,z198,z0,z2,z3,z4,z5]),(0,[z7,z0,z23,z53,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z211,z5]),(0,[z7,z0,z2,z212,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z213]),(1,[z7,z0,z2,z3,z4,z200]),(0,[z7,z0,z2,z3,z214,z4,z5]),(0,[z7,z0,z215,z2,z3,z4,z5]),(0,[z7,z0,z2,z156,z3,z146,z4])],[(0,[z216,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z5,z93]),(0,[z7,z0,z33,z156,z3,z4,z5]),(0,[z7,z0,z132,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z217]),(0,[z7,z102,z0,z2,z3,z94,z5])],[(0,[z0,z1,z2,z3,z4,z36,z5]),(0,[z17,z7,z0,z53,z3,z4,z5]),(0,[z202,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z23,z2,z3,z4,z25]),(0,[z7,z0,z132,z2,z3,z4,z36])],[(0,[z7,z0,z2,z3,z4,z218,z5]),(0,[z219,z130,z0,z2,z3,z4,z5]),(0,[z220,z50,z0,z2,z3,z4,z5]),(0,[z7,z61,z0,z221,z3,z4,z5]),(0,[z222,z7,z0,z2,z3,z4,z5]),(0,[z7,z223,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z224,z3,z4,z5])],[(0,[z0,z1,z2,z156,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z93]),(0,[z7,z0,z106,z2,z3,z4,z5]),(0,[z17,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z125]),(0,[z57,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z225,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z25,z34])],[(0,[z56,z15,z0,z2,z3,z4,z5]),(0,[z17,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z226,z5]),(0,[z7,z0,z2,z227,z3,z4,z5]),(1,[z7,z228,z2,z3,z4,z5]),(0,[z202,z7,z229,z2,z3,z4,z5]),(0,[z7,z0,z230,z2,z3,z4,z5]),(0,[z7,z0,z2,z231,z3,z4,z5]),(0,[z56,z7,z0,z22,z3,z4,z5]),(0,[z57,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z232,z3,z4,z5]),(0,[z233,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z234,z77]),(0,[z7,z0,z2,z3,z4,z5,z235])],[(0,[z15,z0,z132,z2,z3,z4,z5]),(0,[z7,z0,z2,z236,z3,z4,z5]),(0,[z7,z0,z33,z3,z48,z4,z5]),(0,[z7,z0,z22,z3,z4,z237,z5]),(0,[z7,z0,z2,z3,z238,z4,z5]),(0,[z7,z0,z2,z239,z3,z4,z36]),(0,[z240,z7,z0,z2,z3,z4,z5]),(0,[z241,z7,z0,z2,z3,z4,z5]),(0,[z242,z7,z0,z2,z3,z4,z5])],[(0,[z15,z0,z23,z2,z3,z4,z5]),(0,[z243,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z244,z3,z4,z5]),(0,[z245,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z16,z3,z94,z4,z5])]],
   [[(0,[z15,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z246,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z247]),(0,[z7,z0,z2,z3,z4,z5,z119]),(0,[z7,z0,z248,z2,z3,z4,z5]),(1,[z0,z249,z2,z3,z4,z5]),(0,[z7,z250,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z48,z4,z5]),(0,[z7,z251,z0,z33,z3,z4,z5])],[(1,[z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z252,z2,z3,z4,z5]),(0,[z7,z0,z2,z73,z3,z4,z25]),(0,[z219,z7,z0,z2,z3,z4,z36])],[(0,[z0,z1,z2,z3,z8,z4,z5]),(0,[z47,z219,z0,z2,z3,z4,z5]),(0,[z57,z7,z198,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z253,z4,z5]),(0,[z7,z254,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z255])],[(0,[z0,z193,z1,z2,z3,z4,z5]),(0,[z130,z0,z1,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z256,z4,z5]),(0,[z162,z0,z18,z2,z3,z4,z5]),(0,[z202,z7,z0,z2,z3,z4,z74]),(0,[z7,z0,z132,z23,z3,z4,z5])],[(0,[z257,z7,z0,z2,z3,z4,z5]),(0,[z7,z258,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z248,z3,z4,z5]),(0,[z259,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z110,z4,z5,z77])],[(0,[z0,z1,z2,z3,z4,z38,z5]),(0,[z145,z7,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z36,z5]),(0,[z260,z7,z0,z2,z3,z4,z5]),(0,[z7,z261,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z262,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z263]),(0,[z257,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z264,z3,z4,z5]),(0,[z7,z0,z265,z2,z3,z4,z5]),(0,[z7,z50,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z85,z5,z77]),(0,[z7,z0,z2,z3,z4,z5,z266]),(1,[z7,z2,z3,z4,z5,z67]),(0,[z0,z2,z3,z4,z5,z267,z52]),(0,[z7,z0,z2,z27,z3,z4,z52]),(0,[z7,z0,z2,z3,z4,z5,z268])],[(0,[z15,z0,z2,z73,z3,z4,z5]),(0,[z7,z0,z2,z269,z3,z4,z5]),(0,[z7,z0,z53,z3,z4,z5,z255]),(0,[z7,z0,z2,z3,z270,z4,z5]),(0,[z7,z61,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z271,z3,z4,z5]),(0,[z272,z7,z0,z2,z3,z4,z5])]],
   [[(0,[z15,z0,z2,z273,z3,z4,z5]),(0,[z7,z0,z274,z2,z3,z4,z5]),(0,[z7,z0,z275,z2,z3,z4,z5]),(0,[z7,z0,z2,z276,z3,z4,z5])],[(0,[z188,z0,z1,z2,z3,z4,z5]),(1,[z61,z1,z2,z3,z4,z5]),(0,[z162,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z277,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z278,z4,z5]),(0,[z7,z0,z2,z3,z171,z4,z5]),(0,[z7,z0,z22,z3,z4,z5,z77]),(0,[z7,z0,z2,z3,z4,z139,z5]),(1,[z7,z0,z279,z3,z4,z5])],[(0,[z219,z15,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z177]),(0,[z219,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z22,z2,z3,z4,z36]),(0,[z7,z0,z2,z149,z189,z4,z5]),(0,[z7,z0,z2,z3,z4,z25,z280])],[(0,[z47,z7,z0,z2,z48,z4,z5]),(0,[z7,z118,z0,z22,z3,z4,z5]),(0,[z281,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z282,z3,z4,z5])],[(1,[z7,z0,z283,z3,z4,z5]),(0,[z219,z7,z0,z284,z3,z4,z5]),(0,[z7,z198,z0,z2,z3,z4,z285]),(0,[z7,z0,z2,z3,z286,z4,z5]),(0,[z287,z7,z0,z2,z3,z4,z5])],[(0,[z70,z7,z0,z29,z3,z4,z5]),(0,[z7,z0,z288,z2,z3,z4,z5]),(0,[z162,z7,z102,z0,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z289,z5]),(0,[z47,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z290]),(0,[z7,z0,z2,z3,z4,z291,z5])],[(0,[z7,z0,z2,z292,z3,z4,z5]),(0,[z47,z162,z0,z2,z3,z4,z5]),(0,[z7,z293,z0,z2,z3,z4,z5]),(1,[z7,z0,z215,z3,z4,z5]),(0,[z294,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z295,z4,z36]),(0,[z56,z7,z0,z3,z4,z5,z255]),(0,[z7,z0,z2,z110,z3,z24,z5]),(0,[z296,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z84,z2,z3,z4,z5])],[(1,[z15,z0,z33,z3,z4,z5]),(1,[z7,z0,z168,z3,z4,z5]),(0,[z56,z7,z0,z87,z3,z4,z5])]],
   [[(0,[z63,z7,z0,z2,z3,z4,z5]),(0,[z297,z7,z0,z2,z3,z4,z5]),(1,[z220,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z120,z25])],[(0,[z7,z0,z298,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z299,z4,z5]),(0,[z7,z0,z33,z3,z4,z115,z5]),(1,[z7,z0,z3,z300,z4,z5]),(0,[z7,z0,z2,z3,z301,z4,z5]),(0,[z197,z0,z2,z3,z4,z74,z5]),(0,[z7,z10,z0,z22,z3,z4,z5]),(1,[z302,z0,z2,z3,z4,z5]),(0,[z303,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z304]),(0,[z7,z0,z2,z3,z4,z120,z36]),(0,[z296,z0,z2,z3,z4,z5,z52])],[(1,[z15,z1,z2,z3,z4,z5]),(0,[z202,z0,z1,z2,z3,z4,z5]),(0,[z7,z118,z10,z2,z3,z4,z5]),(0,[z7,z0,z22,z22,z3,z4,z5]),(0,[z7,z0,z2,z131,z3,z4,z5]),(0,[z7,z0,z2,z149,z24,z4,z5]),(0,[z7,z0,z2,z305,z3,z4,z5])],[(0,[z10,z0,z1,z2,z3,z4,z5]),(0,[z47,z202,z0,z2,z3,z4,z5]),(0,[z7,z0,z228,z2,z3,z4,z5]),(0,[z7,z0,z2,z165,z3,z4,z5]),(0,[z7,z50,z0,z168,z3,z4,z5]),(0,[z7,z0,z132,z3,z4,z5,z255]),(0,[z7,z0,z2,z3,z4,z5,z306]),(0,[z7,z0,z307,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z115,z5]),(0,[z7,z308,z0,z2,z3,z4,z5]),(0,[z14,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z189,z3,z4,z5]),(0,[z309,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z310]),(0,[z7,z0,z2,z311,z3,z4,z5])],[(0,[z56,z0,z1,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z120,z5]),(0,[z7,z0,z2,z27,z3,z146,z4])],[(0,[z7,z0,z2,z312,z3,z4,z5]),(1,[z7,z10,z33,z3,z4,z5]),(0,[z7,z0,z33,z27,z3,z4,z5]),(0,[z294,z7,z0,z22,z3,z4,z5]),(0,[z7,z198,z0,z2,z3,z4,z313]),(0,[z7,z2,z3,z4,z5,z67,z77])],[(0,[z7,z0,z33,z3,z146,z4,z5]),(0,[z7,z102,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z314])]],
   [[(0,[z7,z0,z0,z2,z3,z4,z5]),(0,[z216,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z315,z5]),(0,[z7,z0,z40,z33,z3,z4,z5]),(0,[z60,z7,z0,z2,z3,z4,z5]),(0,[z7,z102,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z5,z316]),(0,[z7,z0,z317,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z318,z5]),(0,[z7,z0,z2,z319,z3,z4,z5]),(0,[z7,z0,z2,z320,z3,z4,z5])],[(0,[z0,z1,z2,z27,z3,z4,z5]),(0,[z7,z0,z2,z321,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z74,z5]),(0,[z7,z0,z33,z3,z4,z5,z77]),(0,[z7,z322,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z323]),(0,[z7,z0,z3,z94,z4,z5,z255]),(0,[z56,z7,z0,z2,z3,z4,z255]),(0,[z7,z0,z2,z3,z4,z5,z324]),(1,[z7,z0,z134,z3,z4,z5])],[(0,[z0,z1,z2,z3,z146,z4,z5]),(0,[z162,z7,z0,z3,z4,z81,z5]),(0,[z202,z7,z0,z2,z68,z3,z4]),(0,[z7,z325,z0,z2,z3,z4,z5])],[(0,[z70,z7,z105,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z150,z5]),(0,[z7,z105,z0,z2,z3,z4,z25]),(0,[z162,z7,z0,z3,z86,z4,z5]),(0,[z7,z0,z18,z2,z3,z4,z36]),(0,[z7,z326,z0,z2,z3,z4,z5]),(1,[z14,z7,z2,z3,z237,z5]),(0,[z7,z0,z2,z3,z327,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z77]),(0,[z15,z102,z0,z2,z3,z4,z5]),(0,[z328,z7,z0,z2,z3,z4,z5])],[(0,[z0,z1,z157,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z5,z25]),(0,[z7,z329,z0,z2,z3,z4,z5]),(0,[z188,z330,z0,z2,z3,z4,z5]),(1,[z7,z0,z2,z331,z3,z4])],[(0,[z7,z0,z2,z3,z4,z5,z5]),(0,[z7,z0,z33,z3,z85,z4,z5]),(0,[z7,z0,z2,z332,z3,z4,z5]),(0,[z7,z333,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z334,z4,z5]),(0,[z7,z0,z2,z3,z335,z4,z5]),(0,[z7,z336,z0,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z4,z5,z6]),(0,[z302,z118,z0,z2,z3,z4,z5]),(0,[z7,z64,z0,z2,z3,z4,z36]),(0,[z337,z7,z0,z2,z3,z4,z5])]],
   [[(0,[z7,z0,z1,z2,z3,z4,z36]),(0,[z15,z105,z0,z2,z3,z4,z5]),(0,[z98,z7,z0,z2,z48,z4,z5]),(0,[z7,z0,z338,z2,z3,z4,z5]),(0,[z339,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z340,z3,z4,z5]),(1,[z7,z0,z2,z3,z146,z6])],[(0,[z0,z1,z2,z3,z85,z4,z5]),(0,[z7,z0,z2,z53,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z341]),(0,[z197,z7,z0,z2,z3,z4,z93]),(0,[z7,z0,z2,z3,z4,z237,z5]),(0,[z7,z0,z342,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z343])],[(0,[z219,z0,z1,z2,z3,z4,z5]),(0,[z98,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z344,z5]),(1,[z7,z0,z2,z3,z4,z345]),(0,[z7,z0,z2,z68,z3,z4,z36]),(0,[z7,z102,z0,z23,z3,z4,z5])],[(0,[z346,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z5,z255]),(0,[z7,z2,z189,z3,z85,z4,z5])],[(0,[z70,z7,z0,z2,z3,z4,z25]),(0,[z170,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z347,z4,z5]),(0,[z7,z0,z2,z348,z3,z4,z25]),(0,[z349,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z350,z3,z4,z5]),(0,[z7,z0,z2,z3,z351,z4,z5])],[(0,[z70,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z352,z3,z4,z5]),(0,[z7,z0,z33,z204,z3,z4,z5]),(0,[z7,z0,z33,z3,z28,z4,z5])],[(0,[z15,z0,z2,z53,z3,z4,z5]),(0,[z7,z353,z0,z2,z3,z4,z5]),(0,[z7,z354,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z355,z3,z4,z5])],[(1,[z0,z1,z33,z3,z4,z5]),(0,[z7,z356,z0,z2,z3,z4,z5]),(0,[z7,z326,z0,z22,z3,z4,z5]),(0,[z7,z0,z22,z149,z3,z4,z5]),(0,[z7,z64,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z3,z357,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z28,z4,z5]),(0,[z7,z0,z1,z22,z3,z4,z5]),(0,[z162,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z358,z3,z4,z5]),(0,[z7,z0,z2,z3,z85,z4,z25]),(0,[z188,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z359,z4,z5]),(0,[z7,z0,z87,z2,z3,z120,z5])],[(0,[z7,z0,z22,z3,z171,z4,z5]),(0,[z7,z0,z2,z3,z360,z4,z5]),(0,[z14,z7,z50,z2,z3,z4,z5]),(0,[z7,z0,z87,z132,z3,z4,z5])],[(0,[z15,z0,z2,z3,z361,z4,z5]),(0,[z7,z0,z2,z3,z4,z362,z5]),(0,[z7,z0,z2,z3,z4,z5,z363]),(0,[z7,z0,z2,z3,z4,z364,z5]),(0,[z136,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z94,z4,z25]),(0,[z7,z0,z2,z365,z3,z4,z5])],[(0,[z7,z0,z2,z3,z366,z4,z5]),(0,[z7,z0,z2,z3,z237,z5,z77]),(0,[z7,z0,z2,z3,z94,z4,z36]),(1,[z7,z0,z111,z3,z4,z5]),(0,[z7,z0,z2,z3,z367,z4,z5])],[(0,[z14,z0,z1,z2,z3,z4,z5]),(0,[z7,z105,z61,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z91,z4,z5]),(0,[z202,z7,z228,z2,z3,z4,z5]),(0,[z7,z0,z22,z16,z3,z4,z5]),(0,[z368,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z369,z5]),(0,[z7,z0,z2,z370,z3,z4,z5])],[(0,[z70,z15,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z85,z4,z5]),(0,[z7,z0,z2,z3,z371,z4,z5]),(0,[z7,z0,z2,z181,z3,z4,z5]),(0,[z7,z0,z2,z3,z372,z4,z5])],[(0,[z7,z0,z112,z2,z3,z4,z5]),(0,[z373,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z33,z3,z4,z36]),(0,[z374,z7,z0,z2,z3,z4,z5]),(1,[z7,z2,z3,z4,z36,z25])],[(0,[z70,z7,z0,z375,z3,z4,z5]),(0,[z162,z0,z2,z73,z3,z4,z5]),(0,[z130,z7,z0,z2,z3,z171,z5]),(0,[z130,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z36,z93]),(0,[z7,z0,z2,z3,z376,z4,z5]),(0,[z7,z0,z2,z149,z58,z4,z5]),(0,[z7,z0,z2,z377,z3,z4,z5]),(0,[z7,z0,z2,z378,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z379,z77]),(0,[z7,z0,z2,z69,z3,z5,z6])]],
   [[(0,[z7,z380,z0,z2,z3,z4,z5]),(1,[z381,z7,z0,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z382,z5]),(0,[z383,z7,z0,z2,z3,z4,z5])],[(0,[z202,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z35]),(0,[z7,z102,z0,z3,z4,z5,z255])],[(0,[z7,z0,z2,z3,z58,z4,z36]),(0,[z7,z102,z0,z87,z3,z4,z5]),(0,[z7,z0,z2,z384,z3,z4,z5])],[(0,[z7,z0,z54,z73,z3,z4,z5]),(0,[z7,z0,z2,z283,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z5,z255]),(0,[z57,z7,z0,z2,z3,z376,z5]),(0,[z7,z0,z2,z3,z4,z5,z385])],[(0,[z15,z0,z2,z3,z28,z4,z5]),(0,[z386,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z18,z3,z4,z5,z255]),(0,[z7,z0,z2,z3,z4,z387,z5]),(0,[z188,z7,z0,z215,z3,z4,z5]),(0,[z56,z7,z0,z2,z3,z4,z5]),(0,[z7,z388,z0,z2,z3,z4,z5])],[(1,[z7,z0,z389,z3,z4,z5]),(0,[z14,z7,z0,z2,z3,z4,z166]),(0,[z390,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z234]),(0,[z7,z0,z2,z391,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z255]),(0,[z392,z15,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z393,z3,z4,z5]),(0,[z7,z0,z2,z394,z3,z4,z5]),(0,[z7,z0,z2,z3,z395,z4,z5]),(0,[z7,z0,z396,z2,z3,z4,z5])],[(0,[z7,z0,z2,z397,z3,z4,z5]),(0,[z197,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z33,z3,z270,z4,z5]),(0,[z398,z7,z0,z2,z3,z4,z5]),(0,[z7,z198,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z5,z399])]],
   [[(0,[z70,z7,z0,z2,z3,z4,z400]),(0,[z7,z0,z2,z3,z4,z5,z401]),(1,[z7,z0,z54,z3,z4,z5]),(0,[z7,z118,z0,z2,z3,z4,z200]),(0,[z7,z0,z2,z3,z4,z25,z103]),(0,[z7,z0,z2,z3,z4,z402,z5]),(0,[z7,z0,z2,z3,z403,z4,z5]),(0,[z7,z0,z2,z404,z3,z4,z5])],[(0,[z7,z405,z0,z2,z3,z4,z5]),(0,[z7,z0,z33,z3,z171,z4,z5]),(0,[z202,z0,z2,z3,z4,z5,z93]),(0,[z7,z0,z22,z3,z4,z74,z5]),(0,[z57,z7,z0,z2,z3,z406,z5]),(0,[z407,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z408,z3,z4,z5]),(0,[z409,z7,z0,z2,z3,z4,z5]),(0,[z410,z7,z0,z2,z3,z4,z5]),(0,[z411,z7,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z5,z412]),(0,[z7,z0,z2,z413,z3,z4,z5]),(0,[z7,z0,z2,z414,z3,z4,z5]),(1,[z330,z0,z2,z3,z4,z5]),(0,[z56,z7,z0,z2,z3,z4,z81])],[(0,[z47,z7,z0,z2,z73,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z415]),(0,[z7,z0,z22,z3,z4,z81,z5])],[(0,[z0,z1,z2,z3,z171,z4,z5]),(1,[z416,z0,z2,z3,z4,z5]),(0,[z7,z417,z0,z2,z3,z4,z5]),(0,[z7,z0,z156,z279,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z418,z5]),(0,[z7,z0,z2,z3,z4,z5,z419]),(0,[z61,z0,z342,z2,z3,z4,z5])],[(0,[z7,z0,z2,z420,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z345]),(0,[z7,z61,z0,z2,z3,z4,z5]),(0,[z7,z0,z23,z2,z3,z4,z36])],[(0,[z105,z0,z1,z2,z3,z4,z5]),(0,[z197,z15,z0,z2,z3,z4,z5]),(0,[z197,z7,z0,z22,z3,z4,z5])]],
   [[(0,[z7,z421,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z69,z3,z4,z5]),(1,[z57,z7,z2,z58,z4,z5]),(0,[z7,z0,z422,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z266,z25]),(0,[z7,z0,z2,z3,z423,z4,z5]),(0,[z7,z0,z2,z3,z424,z4,z5])],[(0,[z425,z7,z0,z2,z3,z4,z5]),(0,[z426,z7,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z292,z3,z4,z5]),(0,[z219,z7,z0,z2,z3,z4,z5]),(0,[z427,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z428,z4,z5])],[(0,[z429,z7,z0,z2,z3,z4,z5]),(0,[z430,z15,z0,z2,z3,z4,z5]),(0,[z7,z118,z0,z2,z3,z4,z5]),(0,[z7,z2,z3,z85,z4,z237,z5])],[(1,[z7,z0,z106,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z25,z77]),(0,[z7,z0,z431,z2,z3,z4,z5]),(0,[z7,z0,z2,z68,z3,z146,z5])],[(0,[z15,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z33,z189,z3,z4,z5]),(0,[z7,z432,z0,z2,z3,z4,z5]),(0,[z7,z433,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z36,z25])],[(0,[z7,z0,z2,z3,z4,z434,z5]),(0,[z15,z162,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z435,z4,z5]),(0,[z7,z0,z22,z3,z4,z5,z436]),(0,[z7,z0,z2,z3,z4,z36,z36])],[(0,[z47,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z73,z3,z4,z36]),(1,[z7,z0,z33,z3,z4,z5]),(0,[z7,z2,z3,z4,z36,z5,z25]),(0,[z7,z0,z2,z156,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z36,z6]),(0,[z56,z7,z64,z0,z3,z4,z5]),(0,[z7,z0,z2,z3,z437,z4,z5]),(0,[z7,z0,z2,z68,z3,z4,z255]),(0,[z7,z0,z84,z68,z3,z4,z5])],[(0,[z0,z1,z2,z189,z3,z4,z5]),(0,[z47,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z438,z4,z5]),(0,[z14,z7,z2,z189,z3,z4,z5]),(1,[z7,z0,z439,z3,z4,z5]),(0,[z7,z0,z2,z156,z3,z4,z36])]],
   [[(0,[z7,z0,z2,z440,z3,z4,z5]),(0,[z57,z15,z0,z2,z3,z4,z5]),(1,[z15,z0,z2,z3,z4,z25]),(0,[z17,z15,z0,z2,z3,z4,z5]),(0,[z17,z7,z0,z22,z3,z4,z5]),(0,[z219,z0,z2,z73,z3,z4,z5]),(0,[z7,z10,z0,z2,z3,z4,z5]),(0,[z57,z7,z0,z22,z3,z4,z5]),(1,[z7,z0,z22,z3,z4,z25]),(0,[z57,z14,z7,z2,z3,z4,z5]),(0,[z7,z0,z2,z441,z3,z4,z5])],[(1,[z15,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z3,z4,z5]),(0,[z197,z7,z0,z2,z3,z4,z74]),(0,[z7,z0,z33,z3,z4,z74,z5]),(0,[z7,z0,z22,z2,z3,z4,z5]),(0,[z7,z22,z2,z33,z3,z4,z5]),(1,[z7,z0,z22,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z5,z379]),(0,[z7,z388,z0,z3,z4,z5,z52]),(0,[z7,z0,z2,z68,z69,z3,z5])],[(0,[z7,z50,z0,z33,z3,z4,z5]),(0,[z7,z0,z22,z442,z3,z4,z5]),(0,[z7,z0,z2,z149,z3,z4,z5])],[(0,[z443,z7,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z156,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z5,z93]),(0,[z7,z0,z2,z3,z444,z4,z5]),(0,[z7,z0,z2,z3,z48,z4,z25]),(0,[z219,z7,z0,z283,z3,z4,z5]),(1,[z7,z380,z0,z3,z4,z5]),(0,[z7,z445,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z446,z4,z5]),(0,[z7,z44,z0,z2,z3,z4,z5]),(0,[z14,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z447,z2,z3,z4,z5]),(0,[z7,z0,z448,z2,z3,z4,z25]),(0,[z7,z449,z0,z2,z3,z4,z5])],[(0,[z450,z7,z0,z2,z3,z4,z5]),(0,[z451,z7,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z74,z5]),(0,[z0,z2,z73,z3,z48,z4,z5]),(0,[z7,z0,z2,z3,z48,z4,z36]),(1,[z219,z0,z2,z3,z115,z5]),(0,[z452,z7,z0,z22,z3,z4,z5]),(0,[z453,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z454,z3,z4,z5]),(0,[z7,z0,z2,z455,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z175])],[(1,[z7,z0,z2,z3,z4,z150]),(0,[z219,z7,z0,z2,z3,z171,z5]),(0,[z381,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z456,z4,z5]),(0,[z294,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z457,z4,z5]),(0,[z7,z458,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z459,z3,z4,z5]),(0,[z7,z0,z460,z2,z3,z4,z5]),(0,[z7,z0,z2,z189,z3,z4,z25]),(1,[z56,z7,z0,z3,z4,z255]),(1,[z76,z0,z2,z3,z4,z5])],[(1,[z293,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z132,z3,z4,z5]),(0,[z461,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z16,z3,z4,z5]),(0,[z7,z0,z2,z27,z28,z4,z5])]],
   [[(0,[z15,z0,z2,z3,z48,z4,z5]),(0,[z7,z0,z2,z3,z462,z4,z5]),(0,[z98,z7,z0,z2,z73,z4,z5]),(0,[z7,z322,z0,z2,z3,z4,z5]),(0,[z7,z64,z0,z3,z4,z81,z5]),(0,[z7,z463,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z464]),(0,[z465,z7,z0,z2,z3,z4,z5])],[(0,[z466,z0,z1,z2,z3,z4,z5]),(0,[z7,z467,z0,z2,z3,z4,z5]),(0,[z7,z0,z468,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z469,z4,z5]),(0,[z7,z0,z33,z3,z4,z237,z5]),(0,[z7,z0,z3,z86,z4,z5,z255]),(0,[z7,z0,z87,z2,z3,z4,z175]),(1,[z0,z2,z3,z4,z5,z267])],[(0,[z47,z98,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z470,z3,z4,z5])],[(0,[z15,z0,z2,z189,z3,z4,z5]),(0,[z7,z0,z53,z16,z3,z4,z5]),(0,[z7,z0,z2,z151,z3,z4,z5]),(0,[z7,z0,z2,z3,z471,z4,z5])],[(0,[z0,z1,z2,z3,z4,z237,z5]),(0,[z47,z0,z2,z3,z171,z4,z5]),(0,[z7,z0,z2,z3,z472,z4,z5]),(0,[z186,z198,z0,z2,z3,z4,z5]),(0,[z14,z7,z2,z3,z4,z237,z5]),(0,[z7,z0,z2,z3,z24,z4,z5])],[(0,[z57,z7,z2,z3,z85,z4,z5]),(0,[z7,z0,z2,z3,z4,z96,z25])],[(0,[z0,z2,z53,z73,z3,z4,z5]),(0,[z473,z7,z0,z2,z3,z4,z5]),(0,[z474,z7,z0,z2,z3,z4,z5]),(0,[z7,z50,z0,z2,z3,z237,z5]),(0,[z7,z475,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z476,z4,z5])],[(0,[z197,z0,z1,z2,z3,z4,z5]),(0,[z15,z0,z0,z2,z3,z4,z5]),(0,[z477,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z478])]],
   [[(0,[z7,z0,z2,z3,z479,z4,z5]),(0,[z7,z0,z2,z3,z480,z4,z5]),(0,[z7,z0,z87,z3,z4,z81,z5]),(1,[z7,z0,z3,z4,z5,z481])],[(0,[z7,z482,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z203,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z483,z5]),(0,[z7,z0,z87,z3,z86,z4,z5])],[(0,[z7,z0,z18,z2,z3,z4,z5]),(0,[z57,z95,z0,z2,z3,z4,z5]),(0,[z56,z7,z0,z16,z3,z4,z5]),(0,[z7,z0,z2,z484,z3,z4,z5])],[(0,[z113,z7,z0,z2,z3,z4,z5]),(0,[z98,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z485,z5]),(0,[z302,z7,z0,z2,z3,z4,z5])],[(0,[z98,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z0,z33,z3,z4,z5]),(1,[z7,z0,z65,z3,z4,z5]),(0,[z186,z7,z0,z2,z3,z4,z5]),(0,[z7,z102,z0,z2,z3,z120,z5])],[(0,[z7,z0,z2,z3,z486,z4,z5]),(0,[z7,z0,z2,z487,z3,z4,z5]),(0,[z7,z198,z0,z39,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z25,z255])],[(0,[z7,z0,z2,z3,z4,z115,z25]),(0,[z7,z0,z22,z3,z4,z5,z52]),(0,[z7,z0,z2,z488,z3,z4,z36]),(0,[z7,z64,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z81,z5]),(0,[z7,z0,z2,z331,z3,z4,z77]),(0,[z7,z0,z3,z4,z5,z481,z52]),(0,[z7,z0,z69,z384,z3,z4,z5])],[(0,[z7,z0,z1,z2,z3,z4,z5]),(0,[z7,z105,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z115,z36]),(0,[z7,z0,z2,z3,z4,z5,z489]),(0,[z197,z7,z0,z2,z68,z3,z4]),(1,[z7,z0,z2,z3,z4,z313]),(0,[z7,z0,z2,z3,z4,z36,z217]),(0,[z7,z0,z2,z3,z86,z4,z5]),(1,[z0,z82,z2,z3,z4,z5]),(0,[z7,z0,z132,z16,z3,z4,z5]),(0,[z7,z0,z490,z69,z3,z4,z5])]],
   [[(0,[z57,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z25]),(0,[z17,z0,z1,z2,z3,z4,z5]),(0,[z202,z7,z0,z2,z3,z146,z4]),(0,[z7,z0,z2,z491,z3,z4,z5]),(0,[z7,z198,z0,z165,z3,z4,z5]),(1,[z7,z0,z2,z332,z4,z5]),(1,[z492,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z493,z4,z5]),(0,[z7,z0,z494,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z495,z4,z5]),(0,[z57,z7,z0,z122,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z496]),(0,[z7,z0,z2,z3,z497,z4,z5]),(0,[z7,z0,z2,z104,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z498,z5]),(0,[z7,z0,z2,z68,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z499,z5]),(0,[z7,z0,z2,z3,z4,z5,z500]),(0,[z7,z501,z0,z2,z3,z4,z5]),(0,[z7,z50,z0,z2,z3,z85,z5]),(1,[z0,z342,z2,z3,z4,z5]),(0,[z502,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z503,z2,z3,z4,z5]),(0,[z7,z0,z23,z2,z3,z4,z255]),(1,[z7,z121,z0,z3,z4,z5]),(0,[z7,z0,z2,z149,z3,z5,z77])],[(0,[z15,z0,z2,z3,z4,z115,z5]),(0,[z7,z0,z2,z3,z4,z504,z5]),(0,[z7,z501,z0,z33,z3,z4,z5]),(0,[z7,z102,z0,z22,z3,z4,z5]),(0,[z136,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z27,z3,z4,z25]),(0,[z505,z7,z0,z2,z3,z4,z5]),(1,[z7,z0,z431,z3,z4,z5]),(0,[z7,z0,z2,z69,z3,z4,z5])],[(0,[z7,z105,z2,z3,z4,z5,z25]),(0,[z47,z0,z2,z3,z4,z74,z5]),(0,[z202,z7,z0,z389,z3,z4,z5]),(0,[z7,z0,z506,z2,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z387,z5]),(0,[z7,z0,z2,z3,z146,z4,z25]),(0,[z7,z0,z2,z27,z3,z4,z36]),(0,[z7,z64,z0,z132,z3,z4,z5]),(0,[z7,z507,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z53,z3,z4,z36]),(0,[z95,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z508,z5]),(0,[z7,z0,z2,z3,z146,z4,z36]),(0,[z7,z509,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z510,z5]),(0,[z7,z0,z2,z110,z3,z4,z5]),(0,[z7,z0,z2,z3,z511,z4,z5])],[(0,[z130,z7,z0,z2,z3,z4,z5]),(0,[z172,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z159,z5]),(0,[z492,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z87,z2,z3,z4,z5]),(0,[z7,z0,z3,z4,z120,z81,z5]),(0,[z7,z0,z2,z3,z146,z4,z6])],[(0,[z198,z0,z1,z2,z3,z4,z5]),(0,[z130,z7,z0,z33,z3,z4,z5]),(0,[z57,z7,z0,z2,z3,z4,z159]),(0,[z7,z0,z2,z3,z4,z512,z5]),(0,[z7,z160,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z513]),(0,[z7,z0,z2,z68,z3,z4,z81])]],
   [[(0,[z15,z0,z2,z27,z3,z4,z5]),(0,[z7,z0,z3,z300,z4,z115,z5]),(0,[z7,z0,z2,z3,z435,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z436]),(0,[z7,z0,z2,z3,z4,z514,z5]),(0,[z7,z0,z2,z515,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z516,z5]),(0,[z7,z0,z490,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z146,z4,z5]),(0,[z162,z7,z0,z3,z94,z4,z5]),(0,[z7,z0,z2,z3,z4,z36,z255])],[(0,[z7,z0,z2,z3,z4,z517,z5])],[(0,[z15,z0,z2,z3,z4,z5,z77])],[(0,[z7,z0,z2,z2,z3,z4,z5]),(0,[z162,z7,z0,z33,z3,z4,z5]),(1,[z7,z0,z49,z3,z4,z5]),(0,[z7,z518,z0,z2,z3,z4,z5]),(0,[z188,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z519,z4,z5]),(1,[z7,z0,z2,z3,z4,z520]),(0,[z7,z0,z2,z3,z85,z4,z36])],[(0,[z7,z0,z2,z3,z4,z183,z5]),(0,[z7,z0,z2,z442,z3,z4,z5]),(1,[z60,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z521])],[(0,[z522,z7,z0,z2,z3,z4,z5]),(0,[z523,z7,z0,z2,z3,z4,z5]),(0,[z524,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z525,z3,z4,z5]),(0,[z7,z0,z2,z526,z3,z4,z5])],[(0,[z7,z0,z2,z3,z527,z4,z5]),(0,[z7,z0,z2,z528,z3,z4,z5]),(0,[z529,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z191,z2,z3,z4,z36]),(0,[z7,z0,z23,z3,z4,z81,z5]),(0,[z530,z7,z2,z3,z4,z5,z77])]],
   [[(0,[z70,z7,z0,z22,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z25]),(0,[z7,z0,z22,z3,z4,z120,z5])],[(0,[z17,z7,z0,z3,z4,z81,z5]),(0,[z7,z0,z2,z3,z58,z4,z5]),(0,[z7,z0,z2,z189,z4,z5,z77]),(0,[z7,z0,z2,z156,z3,z28,z4])],[(0,[z531,z7,z0,z2,z3,z4,z5]),(0,[z17,z7,z0,z3,z86,z4,z5]),(0,[z7,z198,z2,z189,z3,z4,z5]),(0,[z7,z0,z2,z3,z28,z4,z25]),(1,[z7,z0,z2,z156,z4,z52])],[(0,[z7,z118,z22,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z28,z4,z36]),(0,[z7,z0,z2,z532,z3,z4,z5]),(0,[z7,z0,z2,z279,z3,z4,z5])],[(1,[z70,z1,z2,z3,z4,z5]),(0,[z7,z0,z533,z2,z3,z4,z5]),(0,[z15,z7,z105,z2,z3,z4,z5]),(0,[z7,z0,z534,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z24,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z75]),(0,[z7,z64,z0,z2,z86,z4,z5]),(0,[z7,z0,z2,z3,z535,z4,z5])],[(0,[z7,z536,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z537,z5]),(0,[z202,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z538,z5]),(0,[z7,z0,z2,z539,z3,z4,z5])],[(0,[z130,z7,z0,z2,z3,z115,z5]),(0,[z7,z0,z2,z3,z4,z5,z540]),(0,[z197,z7,z0,z2,z3,z4,z5]),(0,[z7,z229,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z74,z5,z93]),(0,[z7,z198,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z541,z5]),(0,[z7,z0,z2,z3,z542,z4,z5])],[(0,[z15,z0,z2,z3,z4,z5,z401]),(0,[z7,z0,z543,z2,z3,z4,z5]),(1,[z7,z22,z33,z3,z4,z5]),(0,[z7,z0,z544,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z545,z4,z5])]],
   [[(1,[z7,z0,z2,z3,z4,z71]),(0,[z56,z7,z0,z33,z3,z4,z5]),(1,[z7,z0,z2,z3,z4,z88]),(0,[z7,z0,z2,z3,z4,z546,z5])],[(0,[z430,z7,z0,z2,z3,z4,z5]),(0,[z7,z198,z0,z2,z189,z4,z5])],[(0,[z7,z466,z0,z2,z3,z4,z5]),(0,[z162,z7,z0,z18,z3,z4,z5]),(1,[z7,z0,z2,z3,z547,z4]),(0,[z7,z0,z33,z149,z3,z4,z5]),(0,[z7,z0,z2,z3,z548,z4,z5]),(0,[z7,z0,z2,z3,z4,z36,z310])],[(0,[z7,z0,z2,z3,z300,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z313]),(1,[z7,z0,z549,z3,z4,z5]),(0,[z7,z0,z2,z3,z238,z4,z25]),(0,[z7,z0,z550,z2,z3,z4,z5])],[(0,[z0,z1,z22,z2,z3,z4,z5]),(0,[z7,z105,z0,z269,z3,z4,z5]),(0,[z7,z0,z249,z2,z3,z4,z5]),(0,[z50,z0,z422,z2,z3,z4,z5]),(0,[z7,z0,z132,z2,z3,z4,z5]),(1,[z7,z0,z2,z110,z5,z77]),(0,[z7,z551,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z149,z3,z4,z5]),(0,[z15,z0,z2,z420,z3,z4,z5]),(0,[z15,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z33,z3,z456,z4,z5]),(0,[z7,z0,z2,z3,z4,z36,z314]),(0,[z7,z102,z0,z16,z3,z4,z5]),(0,[z7,z0,z2,z552,z3,z4,z5]),(0,[z7,z0,z23,z2,z3,z4,z5])],[(0,[z7,z7,z0,z2,z3,z4,z5]),(0,[z553,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z554,z3,z4,z5]),(0,[z7,z0,z555,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z556])],[(0,[z0,z533,z1,z2,z3,z4,z5]),(0,[z17,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z557,z5]),(0,[z7,z0,z2,z558,z3,z4,z5]),(0,[z10,z293,z0,z2,z3,z4,z5]),(0,[z7,z0,z33,z16,z3,z4,z5]),(0,[z7,z0,z22,z3,z86,z4,z5]),(0,[z57,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z285,z5]),(1,[z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z559,z3,z4,z5])]],
   [[(0,[z7,z0,z18,z16,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z166,z5]),(1,[z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z239,z3,z4,z5])],[(0,[z7,z0,z18,z3,z4,z120,z5]),(0,[z7,z0,z22,z68,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z560]),(0,[z7,z561,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z52]),(0,[z7,z0,z562,z2,z3,z4,z5])],[(0,[z0,z1,z2,z16,z3,z4,z5]),(0,[z7,z0,z2,z563,z3,z4,z5]),(0,[z7,z0,z2,z3,z256,z4,z5]),(0,[z7,z61,z0,z33,z3,z4,z5]),(0,[z7,z198,z0,z22,z3,z4,z5]),(0,[z57,z7,z0,z2,z189,z4,z5])],[(0,[z7,z0,z2,z564,z3,z4,z5]),(0,[z7,z0,z2,z3,z565,z4,z5]),(0,[z452,z7,z0,z2,z3,z4,z5]),(0,[z7,z50,z0,z2,z3,z4,z25]),(0,[z188,z7,z0,z566,z3,z4,z5]),(0,[z7,z0,z23,z2,z3,z4,z81]),(0,[z7,z0,z2,z567,z3,z4,z5]),(0,[z7,z0,z2,z134,z3,z4,z5])],[(0,[z7,z0,z33,z3,z24,z4,z5]),(0,[z198,z0,z249,z2,z3,z4,z5]),(0,[z7,z50,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z149,z3,z4,z25])],[(0,[z15,z0,z2,z3,z4,z5,z255]),(0,[z17,z7,z0,z132,z3,z4,z5]),(0,[z7,z0,z2,z73,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z568]),(0,[z219,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z22,z110,z3,z4,z5]),(0,[z7,z0,z2,z276,z3,z4,z25]),(0,[z7,z569,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z570,z3,z4,z5])],[(0,[z7,z0,z2,z273,z3,z4,z5]),(0,[z7,z0,z2,z3,z171,z4,z25]),(0,[z571,z7,z0,z2,z3,z4,z5]),(0,[z7,z118,z0,z33,z3,z4,z5]),(1,[z7,z0,z2,z572,z4,z5]),(0,[z188,z492,z0,z2,z3,z4,z5]),(0,[z7,z64,z102,z0,z3,z4,z5])],[(0,[z0,z1,z2,z3,z24,z4,z5]),(0,[z15,z10,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z88,z5])]],
   [[(0,[z70,z0,z1,z2,z3,z4,z5]),(0,[z15,z50,z0,z2,z3,z4,z5]),(0,[z7,z573,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z574])],[(0,[z15,z0,z2,z149,z3,z4,z5]),(0,[z15,z98,z0,z2,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z483,z5]),(0,[z7,z0,z2,z575,z3,z4,z5]),(1,[z296,z0,z2,z3,z4,z5])],[(1,[z7,z0,z375,z3,z4,z5]),(0,[z15,z7,z1,z2,z3,z4,z5]),(0,[z7,z105,z0,z2,z3,z4,z177]),(1,[z7,z0,z2,z3,z4,z11]),(0,[z7,z0,z22,z3,z94,z4,z5]),(0,[z7,z0,z2,z3,z4,z576,z5])],[(0,[z257,z15,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z171,z4,z5]),(0,[z7,z0,z2,z3,z4,z577,z5]),(0,[z7,z0,z2,z3,z4,z406,z5]),(0,[z578,z7,z0,z2,z3,z4,z5]),(0,[z7,z579,z0,z2,z3,z4,z5]),(0,[z7,z580,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z581,z4,z5]),(0,[z7,z10,z0,z33,z3,z4,z5]),(0,[z14,z7,z0,z2,z572,z4,z5]),(0,[z7,z582,z0,z2,z3,z4,z5]),(0,[z7,z583,z0,z2,z3,z4,z5])],[(0,[z0,z1,z18,z2,z3,z4,z5]),(0,[z7,z0,z584,z2,z3,z4,z5]),(0,[z7,z0,z22,z33,z3,z4,z5]),(0,[z7,z0,z2,z585,z3,z4,z5]),(0,[z63,z7,z0,z2,z3,z4,z25])],[(0,[z7,z0,z2,z3,z547,z4,z5]),(0,[z586,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z81,z5]),(0,[z461,z7,z0,z2,z3,z4,z5])],[(0,[z15,z0,z288,z2,z3,z4,z5]),(0,[z7,z587,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z588,z4,z5]),(0,[z14,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z33,z3,z86,z4,z5]),(0,[z589,z7,z0,z2,z3,z4,z5]),(1,[z245,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z590,z5])]],
   [[(0,[z135,z0,z1,z2,z3,z4,z5]),(0,[z7,z591,z0,z2,z3,z4,z5]),(0,[z589,z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z295,z4,z5]),(0,[z14,z7,z0,z439,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z81,z5]),(0,[z7,z0,z33,z68,z3,z4,z5]),(0,[z7,z0,z22,z3,z58,z4,z5]),(0,[z7,z0,z2,z592,z3,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z86,z4,z5]),(0,[z47,z15,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z593,z4,z5]),(0,[z47,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z189,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z36,z77]),(0,[z7,z0,z132,z2,z86,z4,z5]),(0,[z7,z0,z2,z69,z3,z146,z4])],[(1,[z7,z0,z2,z3,z4,z400]),(0,[z7,z0,z33,z69,z3,z4,z5]),(0,[z7,z0,z2,z3,z594,z4,z5]),(0,[z7,z0,z2,z3,z4,z120,z5]),(0,[z7,z0,z595,z2,z3,z4,z5]),(0,[z7,z596,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z331,z3,z4,z5])],[(0,[z0,z1,z2,z68,z3,z4,z5]),(1,[z15,z0,z22,z3,z4,z5]),(0,[z219,z7,z0,z2,z3,z115,z5]),(0,[z7,z0,z2,z3,z4,z38,z36]),(0,[z7,z64,z0,z3,z86,z4,z5])],[(0,[z597,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z33,z110,z3,z4,z5]),(0,[z7,z0,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z111,z3,z4,z5]),(0,[z7,z0,z2,z598,z3,z4,z5])],[(0,[z0,z1,z2,z69,z3,z4,z5]),(0,[z7,z0,z599,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z74,z25]),(1,[z7,z0,z2,z3,z4,z508]),(0,[z7,z0,z0,z2,z3,z4,z36])],[(0,[z600,z15,z0,z2,z3,z4,z5]),(0,[z7,z0,z53,z3,z4,z120,z5]),(0,[z7,z0,z2,z3,z4,z601,z5]),(0,[z7,z0,z448,z22,z3,z4,z5]),(0,[z309,z7,z0,z2,z3,z4,z5]),(0,[z46,z7,z0,z2,z3,z4,z36]),(1,[z7,z388,z0,z3,z4,z5]),(0,[z7,z0,z2,z602,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z110,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z603,z5]),(1,[z7,z0,z2,z3,z4,z285]),(0,[z7,z0,z2,z604,z3,z4,z5])],[(0,[z0,z1,z87,z2,z3,z4,z5]),(1,[z162,z0,z18,z3,z4,z5]),(0,[z7,z0,z2,z605,z3,z4,z5]),(0,[z202,z7,z0,z2,z3,z4,z93]),(0,[z7,z0,z2,z3,z327,z4,z36])],[(0,[z7,z0,z2,z3,z547,z4,z115]),(0,[z7,z0,z2,z606,z3,z4,z5]),(0,[z7,z50,z0,z2,z3,z4,z508]),(0,[z7,z102,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z607,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z608])],[(0,[z50,z0,z1,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z74,z5]),(0,[z7,z0,z22,z18,z3,z4,z5]),(0,[z609,z7,z0,z2,z3,z4,z5]),(0,[z202,z7,z0,z49,z3,z4,z5]),(0,[z14,z7,z0,z2,z3,z237,z5]),(0,[z7,z0,z2,z3,z4,z5,z25])],[(0,[z610,z7,z0,z2,z3,z4,z5]),(1,[z7,z0,z3,z4,z5,z263]),(0,[z7,z0,z2,z3,z4,z5,z611])],[(1,[z7,z0,z269,z3,z4,z5]),(1,[z7,z0,z2,z3,z4,z125]),(0,[z7,z0,z2,z488,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z6])],[(0,[z7,z105,z0,z2,z3,z4,z5]),(0,[z7,z0,z18,z33,z3,z4,z5]),(0,[z7,z198,z0,z2,z58,z4,z5]),(0,[z7,z0,z2,z3,z4,z237,z25]),(0,[z7,z0,z2,z3,z612,z4,z5]),(0,[z56,z7,z0,z3,z4,z120,z5]),(0,[z7,z0,z2,z3,z4,z613,z5]),(0,[z530,z7,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z30,z4,z5]),(0,[z46,z15,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z614,z4,z5]),(0,[z57,z7,z0,z2,z3,z4,z345]),(0,[z7,z0,z2,z3,z4,z237,z36]),(0,[z7,z64,z0,z3,z94,z4,z5]),(0,[z7,z0,z2,z3,z615,z4,z5])]],
   [[(0,[z616,z7,z0,z2,z3,z4,z5]),(0,[z130,z7,z0,z2,z3,z4,z25]),(0,[z7,z117,z0,z2,z3,z4,z5]),(1,[z7,z0,z566,z3,z4,z5]),(0,[z7,z0,z3,z4,z81,z5,z255]),(0,[z7,z0,z431,z156,z3,z4,z5])],[(0,[z7,z0,z33,z3,z58,z4,z5]),(1,[z7,z0,z2,z3,z4,z119]),(0,[z7,z0,z2,z3,z4,z5,z617]),(0,[z7,z121,z0,z3,z4,z5,z77]),(0,[z618,z7,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z5,z619]),(0,[z138,z7,z0,z2,z3,z4,z5]),(0,[z7,z64,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z34]),(0,[z7,z0,z2,z620,z3,z4,z5]),(0,[z7,z0,z2,z621,z3,z4,z5])],[(0,[z7,z0,z1,z33,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z237,z5]),(0,[z162,z7,z0,z53,z3,z4,z5]),(0,[z98,z7,z0,z622,z3,z4,z5]),(0,[z7,z0,z132,z3,z4,z120,z5])],[(0,[z0,z1,z2,z3,z58,z4,z5]),(0,[z7,z0,z2,z53,z3,z4,z5]),(0,[z219,z0,z2,z3,z4,z115,z5]),(0,[z7,z0,z22,z3,z4,z36,z5]),(0,[z7,z0,z2,z3,z24,z237,z5]),(0,[z7,z0,z2,z623,z3,z4,z5])],[(0,[z17,z0,z2,z53,z3,z4,z5]),(0,[z162,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z5,z624]),(0,[z7,z0,z2,z3,z4,z5,z625]),(0,[z7,z0,z22,z73,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z626]),(0,[z7,z380,z0,z3,z4,z115,z5]),(0,[z197,z7,z0,z2,z3,z146,z4]),(0,[z188,z7,z0,z2,z3,z4,z25]),(1,[z530,z7,z2,z3,z4,z5]),(0,[z7,z0,z627,z2,z3,z4,z5])],[(0,[z162,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z22,z3,z4,z5,z93]),(0,[z7,z0,z22,z156,z3,z4,z5]),(0,[z7,z2,z189,z3,z58,z4,z5]),(0,[z188,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z628,z2,z3,z4,z5])],[(0,[z70,z7,z0,z2,z3,z4,z5]),(0,[z7,z629,z0,z2,z3,z4,z5]),(0,[z17,z7,z102,z0,z3,z4,z5]),(0,[z98,z7,z0,z22,z3,z4,z5]),(0,[z57,z7,z0,z2,z58,z4,z5]),(0,[z14,z7,z0,z2,z3,z85,z5]),(0,[z7,z0,z2,z348,z3,z4,z5]),(0,[z136,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z87,z3,z94,z4,z5])]],
   [[(0,[z7,z0,z2,z3,z361,z4,z5]),(0,[z630,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z631,z5]),(1,[z7,z0,z131,z3,z4,z5]),(0,[z632,z7,z0,z2,z3,z4,z5])],[(0,[z7,z633,z0,z2,z3,z4,z5]),(0,[z634,z7,z0,z2,z3,z4,z5]),(0,[z635,z7,z0,z2,z3,z4,z5]),(0,[z636,z7,z0,z2,z3,z4,z5]),(0,[z14,z7,z0,z2,z332,z4,z5]),(0,[z7,z0,z3,z94,z4,z120,z5]),(0,[z7,z0,z2,z3,z637,z4,z5])],[(0,[z64,z0,z1,z2,z3,z4,z5]),(0,[z47,z0,z1,z2,z3,z4,z5]),(0,[z7,z105,z0,z22,z3,z4,z5]),(0,[z7,z0,z638,z2,z3,z4,z5]),(0,[z381,z7,z0,z3,z4,z5,z93]),(0,[z7,z0,z87,z33,z3,z4,z5]),(0,[z7,z0,z2,z639,z3,z4,z5])],[(1,[z7,z0,z29,z3,z4,z5]),(0,[z7,z0,z22,z3,z48,z4,z5]),(0,[z7,z0,z2,z3,z640,z4,z5]),(0,[z7,z0,z22,z3,z4,z577,z5]),(0,[z188,z7,z2,z3,z4,z5,z25]),(0,[z7,z0,z2,z3,z641,z4,z5])],[(1,[z0,z1,z22,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z362,z5]),(0,[z7,z0,z2,z642,z3,z4,z5]),(0,[z7,z0,z126,z22,z3,z4,z5]),(0,[z7,z0,z2,z643,z3,z4,z5])],[(0,[z7,z0,z2,z377,z3,z4,z36]),(0,[z7,z0,z2,z3,z94,z4,z5]),(0,[z7,z0,z2,z3,z4,z124,z77])],[(0,[z130,z0,z2,z3,z171,z4,z5]),(0,[z202,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z644,z4,z5]),(0,[z7,z0,z2,z645,z3,z4,z5]),(0,[z7,z0,z2,z646,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z5,z400]),(0,[z0,z1,z132,z2,z3,z4,z5]),(0,[z136,z15,z0,z2,z3,z4,z5]),(1,[z47,z0,z2,z48,z4,z5]),(0,[z202,z7,z0,z2,z3,z4,z36]),(0,[z136,z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z140,z22,z3,z4,z5]),(0,[z7,z0,z2,z647,z3,z4,z5])]],
   [[(0,[z0,z1,z23,z2,z3,z4,z5]),(0,[z392,z7,z0,z2,z3,z4,z5]),(0,[z7,z64,z0,z18,z3,z4,z5]),(0,[z7,z648,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z32,z3,z4,z5]),(0,[z7,z0,z606,z33,z3,z4,z5]),(0,[z7,z0,z2,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z280])],[(0,[z56,z162,z7,z0,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z5,z52]),(0,[z7,z0,z2,z439,z3,z4,z5]),(0,[z56,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z649,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z650])],[(0,[z7,z0,z3,z4,z5,z263,z93]),(0,[z7,z0,z2,z651,z3,z4,z5]),(0,[z7,z0,z33,z563,z3,z4,z5]),(0,[z118,z117,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z652,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z387,z36]),(0,[z76,z7,z0,z2,z3,z4,z5])],[(0,[z7,z0,z157,z22,z3,z4,z5]),(0,[z7,z0,z23,z3,z86,z4,z5])],[(0,[z118,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z52]),(0,[z7,z0,z53,z33,z3,z4,z5]),(0,[z653,z7,z0,z2,z3,z4,z5]),(1,[z202,z0,z2,z3,z4,z93]),(0,[z7,z0,z2,z654,z3,z4,z5]),(0,[z655,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z656,z3,z4,z5]),(0,[z7,z657,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z563,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z148]),(0,[z7,z0,z622,z2,z3,z4,z5]),(0,[z7,z0,z33,z73,z3,z4,z5]),(0,[z14,z7,z0,z2,z3,z4,z520]),(0,[z658,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z659,z3,z4,z5]),(0,[z7,z0,z2,z3,z660,z4,z5]),(0,[z7,z0,z2,z3,z661,z4,z5])],[(0,[z0,z18,z2,z53,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z662]),(1,[z7,z0,z2,z3,z376,z5]),(0,[z220,z7,z0,z2,z3,z4,z5]),(0,[z7,z330,z0,z2,z3,z4,z5]),(0,[z188,z7,z61,z2,z3,z4,z5]),(0,[z7,z663,z0,z2,z3,z4,z5]),(0,[z7,z0,z664,z2,z3,z4,z5]),(0,[z7,z0,z2,z665,z3,z4,z5])],[(0,[z202,z15,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z666]),(0,[z667,z7,z0,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z73,z3,z4,z5]),(0,[z7,z0,z87,z18,z3,z4,z5]),(0,[z7,z416,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z195,z4,z5])],[(0,[z7,z0,z375,z2,z3,z4,z5]),(0,[z57,z416,z0,z2,z3,z4,z5]),(0,[z7,z668,z0,z2,z3,z4,z5]),(0,[z7,z669,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z670,z5])],[(0,[z15,z130,z0,z2,z3,z4,z5]),(0,[z197,z7,z0,z33,z3,z4,z5]),(0,[z7,z198,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z671,z4,z5]),(0,[z245,z0,z132,z2,z3,z4,z5])],[(0,[z7,z672,z0,z2,z3,z4,z5]),(0,[z7,z673,z0,z2,z3,z4,z5]),(0,[z7,z0,z544,z33,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z5,z25]),(0,[z7,z61,z0,z2,z3,z4,z25])],[(0,[z674,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z32,z3,z4,z115]),(1,[z172,z0,z2,z3,z4,z5]),(1,[z7,z0,z2,z3,z406,z5]),(0,[z7,z61,z0,z2,z3,z4,z36]),(0,[z0,z132,z82,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z675]),(0,[z56,z7,z0,z23,z3,z4,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z185,z5]),(0,[z676,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z677,z3,z4,z5]),(0,[z7,z251,z0,z2,z3,z4,z5]),(0,[z7,z678,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z679,z4,z5]),(1,[z281,z0,z2,z3,z4,z5]),(0,[z7,z0,z221,z2,z3,z4,z5])],[(0,[z61,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z284,z2,z3,z4,z5]),(0,[z219,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z22,z3,z4,z115,z5]),(0,[z7,z0,z2,z680,z3,z4,z5]),(1,[z7,z0,z358,z3,z4,z5]),(0,[z7,z0,z23,z3,z94,z4,z5]),(0,[z7,z0,z2,z156,z4,z5,z52])],[(0,[z98,z0,z1,z2,z3,z4,z5]),(0,[z7,z681,z0,z2,z3,z4,z5]),(0,[z7,z118,z0,z2,z3,z4,z25]),(1,[z7,z0,z221,z3,z4,z5])]],
   [[(0,[z15,z61,z0,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z5,z52]),(0,[z17,z7,z0,z3,z94,z4,z5]),(0,[z197,z202,z0,z2,z3,z4,z5]),(0,[z7,z0,z132,z33,z3,z4,z5]),(0,[z7,z118,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z110,z3,z5,z77])],[(0,[z15,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z682,z4,z5]),(0,[z7,z0,z2,z683,z3,z4,z5]),(0,[z7,z0,z23,z33,z3,z4,z5]),(0,[z7,z102,z0,z3,z4,z120,z5])],[(0,[z7,z0,z2,z684,z3,z4,z5]),(1,[z7,z0,z3,z91,z4,z5]),(0,[z7,z50,z0,z358,z3,z4,z5]),(0,[z7,z0,z2,z3,z685,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z481])],[(0,[z17,z7,z0,z33,z3,z4,z5]),(0,[z57,z7,z0,z33,z3,z4,z5]),(1,[z7,z0,z33,z3,z4,z25]),(0,[z7,z0,z33,z3,z4,z120,z5]),(0,[z7,z0,z22,z27,z3,z4,z5]),(0,[z14,z281,z0,z2,z3,z4,z5]),(0,[z7,z686,z0,z2,z3,z4,z5])],[(0,[z15,z118,z0,z2,z3,z4,z5]),(0,[z17,z162,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z53,z3,z4,z5]),(1,[z7,z0,z33,z3,z4,z36]),(0,[z7,z0,z22,z3,z146,z4,z5]),(0,[z14,z7,z0,z549,z3,z4,z5]),(1,[z0,z422,z2,z3,z4,z5])],[(0,[z98,z7,z0,z151,z3,z4,z5]),(0,[z7,z10,z0,z2,z3,z4,z25]),(0,[z7,z0,z87,z2,z3,z94,z5]),(0,[z687,z7,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z120,z5]),(1,[z7,z1,z2,z3,z4,z25]),(0,[z7,z10,z0,z2,z3,z4,z36]),(0,[z7,z0,z22,z2,z3,z4,z25]),(0,[z7,z0,z2,z65,z3,z4,z5]),(0,[z688,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z689,z2,z3,z4,z5]),(0,[z7,z64,z0,z2,z16,z4,z5])],[(0,[z136,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z690,z4,z5]),(1,[z7,z0,z622,z3,z4,z5]),(0,[z7,z0,z22,z3,z158,z4,z5]),(0,[z7,z0,z2,z566,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z36,z5])]],
   [[(0,[z7,z61,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z691,z3,z4,z5]),(0,[z14,z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z149,z3,z4,z36]),(1,[z7,z0,z384,z3,z4,z5])],[(0,[z15,z15,z0,z2,z3,z4,z5]),(0,[z15,z7,z0,z22,z3,z4,z5]),(0,[z47,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z692,z5]),(0,[z7,z0,z389,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z93]),(0,[z7,z0,z549,z2,z3,z4,z5]),(0,[z14,z7,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z454,z3,z4,z25]),(0,[z7,z0,z2,z3,z693,z4,z5]),(0,[z7,z0,z2,z156,z3,z4,z5]),(0,[z694,z7,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z71,z5]),(0,[z7,z0,z2,z3,z695,z4,z5]),(0,[z0,z2,z73,z3,z171,z4,z5]),(0,[z7,z0,z2,z3,z171,z4,z36]),(0,[z7,z0,z2,z3,z4,z696,z5]),(0,[z7,z0,z2,z3,z697,z4,z5]),(0,[z7,z0,z2,z698,z3,z4,z5])],[(1,[z15,z0,z2,z3,z4,z5]),(0,[z15,z0,z22,z2,z3,z4,z5]),(1,[z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z5,z25]),(0,[z7,z0,z22,z3,z85,z4,z5]),(0,[z7,z0,z2,z3,z4,z5,z520]),(0,[z7,z0,z2,z3,z4,z5,z699]),(1,[z7,z0,z3,z4,z5,z234]),(0,[z7,z0,z2,z68,z156,z3,z4]),(1,[z7,z0,z490,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z700,z5]),(0,[z7,z0,z2,z3,z4,z25,z148]),(0,[z7,z0,z2,z16,z3,z4,z25]),(0,[z7,z0,z2,z3,z146,z4,z255]),(0,[z7,z0,z2,z3,z4,z5,z701])],[(0,[z702,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z703,z2,z3,z4,z5]),(1,[z7,z0,z284,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z572,z4,z5]),(1,[z188,z7,z2,z3,z4,z25]),(0,[z7,z0,z2,z16,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z36,z81]),(0,[z704,z7,z0,z2,z3,z4,z5]),(0,[z7,z705,z0,z2,z3,z4,z5]),(1,[z0,z2,z3,z4,z5,z379]),(0,[z7,z0,z2,z3,z4,z5,z267])],[(0,[z0,z1,z2,z3,z4,z5,z25]),(0,[z600,z7,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z48,z4,z5]),(1,[z7,z229,z2,z3,z4,z5]),(0,[z7,z0,z448,z2,z3,z4,z5])],[(0,[z706,z7,z0,z2,z3,z4,z5]),(0,[z7,z50,z0,z22,z3,z4,z5]),(1,[z44,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z27,z68,z3,z4])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z384,z3,z4,z5]),(0,[z216,z0,z2,z3,z4,z93]),(0,[z707,z7,z2,z3,z4,z5]),(0,[z7,z0,z165,z3,z4,z5]),(0,[z7,z0,z111,z3,z4,z36]),(0,[z7,z102,z0,z3,z120,z5])],[(0,[z7,z0,z3,z4,z5,z708]),(0,[z0,z22,z3,z4,z5,z379]),(0,[z709,z0,z2,z3,z4,z5]),(0,[z0,z2,z156,z4,z267,z52])],[(0,[z7,z0,z710,z3,z4,z5]),(0,[z380,z0,z1,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z711]),(0,[z7,z0,z712,z3,z4,z25])],[(0,[z1,z2,z3,z4,z74,z25])],[(0,[z7,z0,z2,z3,z4,z713])],[(0,[z7,z0,z2,z3,z714,z5]),(0,[z7,z715,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z716,z5]),(0,[z717,z0,z2,z3,z4,z5]),(0,[z718,z0,z2,z3,z4,z5]),(0,[z76,z121,z0,z3,z4,z5]),(0,[z7,z0,z719,z3,z4,z5])],[(0,[z17,z449,z0,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z720])],[(0,[z7,z105,z2,z3,z4,z25]),(0,[z674,z7,z0,z3,z4,z255]),(0,[z7,z22,z154,z3,z4,z5])],[(0,[z381,z202,z0,z3,z4,z93]),(0,[z7,z0,z439,z3,z4,z520])],[(0,[z7,z0,z3,z721,z4,z5]),(0,[z7,z0,z389,z3,z4,z25]),(0,[z7,z722,z0,z3,z4,z5]),(0,[z7,z0,z723,z3,z4,z5])],[(0,[z15,z0,z2,z3,z4,z159]),(0,[z7,z353,z2,z3,z4,z25]),(0,[z7,z0,z724,z3,z4,z5]),(0,[z7,z0,z2,z3,z238,z280])],[(0,[z202,z0,z2,z3,z4,z93]),(0,[z7,z0,z725,z3,z4,z5])],[(0,[z7,z0,z54,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z726]),(0,[z7,z0,z22,z3,z4,z166]),(0,[z7,z0,z727,z3,z4,z25])],[(0,[z7,z0,z22,z3,z4,z175]),(0,[z296,z0,z2,z156,z4,z52])],[(0,[z1,z33,z3,z58,z4,z5]),(0,[z15,z0,z2,z3,z4,z124])],[(0,[z162,z0,z3,z97,z4,z5]),(0,[z7,z0,z728,z3,z4,z5]),(0,[z7,z33,z3,z4,z237,z25]),(0,[z7,z33,z3,z612,z4,z5]),(0,[z7,z0,z2,z729,z4,z5])]],
   [[(0,[z730,z0,z2,z3,z4,z5]),(0,[z7,z0,z731,z3,z4,z5]),(0,[z732,z0,z2,z3,z4,z5])],[(0,[z136,z1,z2,z3,z4,z25]),(0,[z733,z7,z0,z3,z4,z5]),(0,[z416,z0,z2,z3,z4,z36]),(0,[z95,z0,z2,z3,z4,z345]),(0,[z7,z0,z3,z4,z5,z734]),(0,[z7,z0,z2,z3,z735,z4]),(0,[z736,z0,z2,z3,z4,z5])],[(0,[z7,z0,z3,z4,z5,z737]),(0,[z7,z0,z738,z3,z4,z5]),(0,[z739,z0,z2,z3,z4,z5]),(0,[z740,z0,z2,z3,z4,z5])],[(0,[z202,z0,z2,z3,z4,z310]),(0,[z7,z0,z2,z3,z4,z741]),(0,[z7,z0,z742,z3,z4,z5])],[(0,[z7,z0,z375,z3,z4,z71]),(0,[z7,z743,z2,z3,z4,z5]),(0,[z744,z0,z2,z3,z4,z5]),(0,[z7,z0,z745,z3,z4,z5])],[(0,[z0,z1,z2,z3,z146,z6]),(0,[z390,z0,z18,z3,z4,z5]),(0,[z228,z2,z3,z4,z5,z93]),(0,[z281,z0,z33,z3,z4,z5]),(0,[z57,z7,z2,z58,z4,z36]),(0,[z7,z0,z3,z4,z36,z481])],[(0,[z7,z0,z2,z3,z4,z5]),(0,[z746,z0,z2,z3,z4,z5]),(0,[z7,z322,z0,z3,z139,z5]),(0,[z7,z0,z747,z3,z4,z5])],[(0,[z1,z2,z639,z3,z4,z5]),(0,[z330,z0,z22,z3,z4,z5]),(0,[z530,z7,z2,z331,z3,z4])],[(0,[z1,z2,z3,z640,z4,z5]),(0,[z405,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z748]),(0,[z7,z0,z122,z3,z4,z345]),(0,[z7,z0,z2,z572,z4,z36])],[(0,[z416,z0,z22,z3,z4,z5])],[(0,[z7,z0,z749,z3,z4,z5]),(0,[z7,z380,z0,z3,z547,z4]),(0,[z202,z0,z2,z3,z535,z4]),(0,[z296,z0,z2,z3,z4,z25]),(0,[z7,z750,z2,z3,z4,z5]),(0,[z7,z0,z2,z751,z5,z77])],[(0,[z417,z1,z2,z3,z4,z5]),(0,[z7,z752,z0,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z36]),(0,[z7,z0,z439,z3,z4,z25]),(0,[z7,z0,z753,z86,z4,z5]),(0,[z7,z0,z2,z3,z751,z5])],[(0,[z7,z0,z754,z3,z4,z5]),(0,[z0,z422,z33,z3,z4,z5]),(0,[z0,z755,z2,z3,z4,z5])],[(0,[z57,z7,z22,z58,z4,z5]),(0,[z7,z0,z2,z3,z4,z756]),(0,[z7,z0,z84,z3,z4,z175])],[(0,[z7,z0,z757,z3,z4,z5]),(0,[z7,z758,z0,z3,z4,z5]),(0,[z7,z0,z759,z3,z4,z5])],[(0,[z7,z380,z0,z3,z4,z25])]],
   [[(0,[z15,z0,z106,z3,z4,z5]),(0,[z7,z0,z283,z3,z4,z5])],[(0,[z219,z0,z2,z3,z115,z36]),(0,[z760,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z332,z4,z520])],[(0,[z0,z1,z2,z3,z4,z159]),(0,[z1,z2,z3,z660,z4,z5]),(0,[z7,z506,z2,z3,z4,z25]),(0,[z7,z0,z761,z3,z4,z5]),(0,[z7,z0,z439,z572,z4,z5])],[(0,[z1,z2,z3,z4,z5,z662]),(0,[z293,z0,z2,z3,z4,z25]),(0,[z7,z0,z762,z3,z4,z5]),(0,[z220,z0,z358,z3,z4,z5]),(0,[z76,z0,z2,z3,z4,z36])],[(0,[z7,z0,z763,z3,z4,z5]),(0,[z7,z0,z764,z3,z4,z5]),(0,[z765,z0,z2,z3,z4,z5])],[(0,[z162,z0,z288,z3,z4,z5]),(0,[z7,z669,z33,z3,z4,z5]),(0,[z766,z0,z2,z3,z4,z5]),(0,[z767,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z124]),(0,[z7,z0,z768,z3,z4,z5]),(0,[z63,z228,z2,z3,z4,z5]),(0,[z7,z0,z2,z769,z3,z5])],[(0,[z7,z0,z770,z3,z4,z5]),(0,[z44,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z771,z3,z4]),(0,[z60,z0,z131,z3,z4,z5])],[(0,[z7,z0,z772,z3,z4,z5]),(0,[z466,z0,z563,z3,z4,z5]),(0,[z162,z0,z773,z3,z4,z5]),(0,[z7,z0,z3,z774,z4,z5])],[(0,[z7,z0,z2,z775,z4,z5]),(0,[z7,z0,z2,z3,z4,z35])],[(0,[z7,z0,z22,z3,z4,z150]),(0,[z7,z0,z3,z4,z5,z776]),(0,[z7,z0,z33,z32,z3,z4]),(0,[z7,z0,z777,z3,z4,z5]),(0,[z7,z0,z778,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z779]),(0,[z76,z0,z22,z3,z4,z5]),(0,[z780,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z781])],[(1,[z1,z2,z3,z4,z400]),(0,[z118,z1,z22,z3,z4,z5]),(0,[z13,z0,z2,z3,z115,z5]),(0,[z7,z0,z782,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z783]),(0,[z47,z0,z49,z3,z4,z5]),(0,[z0,z151,z73,z3,z4,z5]),(0,[z7,z0,z3,z784,z4,z5]),(0,[z293,z0,z2,z3,z4,z11]),(0,[z117,z0,z2,z3,z4,z200])],[(0,[z15,z0,z168,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z785]),(0,[z786,z0,z2,z3,z4,z5]),(0,[z7,z0,z787,z3,z4,z5]),(0,[z7,z0,z788,z3,z4,z5]),(0,[z789,z0,z2,z3,z4,z5])]],
   [[(0,[z7,z251,z0,z86,z4,z5]),(0,[z188,z7,z215,z3,z4,z25])],[(0,[z7,z1,z2,z3,z4,z400]),(0,[z15,z0,z3,z300,z4,z5]),(0,[z7,z0,z33,z3,z4,z508]),(0,[z302,z0,z22,z3,z4,z5]),(0,[z7,z0,z65,z3,z4,z36]),(0,[z7,z0,z2,z414,z5,z77]),(0,[z7,z0,z2,z790,z3,z4]),(0,[z7,z0,z3,z4,z36,z791])],[(0,[z7,z0,z2,z3,z792,z5]),(0,[z7,z0,z566,z3,z4,z36]),(0,[z7,z0,z3,z793,z4,z5]),(0,[z7,z0,z84,z3,z4,z5]),(0,[z296,z388,z0,z3,z4,z5])],[(0,[z1,z22,z2,z3,z4,z25]),(0,[z7,z0,z794,z3,z4,z5]),(0,[z7,z579,z2,z3,z4,z25]),(0,[z7,z0,z623,z3,z4,z255]),(0,[z530,z7,z2,z110,z5,z77])],[(0,[z7,z0,z2,z3,z4,z795]),(0,[z1,z2,z149,z3,z4,z25]),(0,[z257,z0,z288,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z796]),(0,[z7,z0,z797,z3,z4,z5]),(0,[z7,z0,z2,z332,z4,z25])],[(0,[z47,z0,z2,z798,z4,z5]),(0,[z95,z0,z33,z3,z4,z5]),(0,[z492,z0,z2,z3,z4,z36]),(0,[z7,z0,z799,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z800])],[(0,[z533,z1,z2,z3,z4,z25]),(0,[z1,z2,z3,z4,z692,z5]),(0,[z452,z0,z18,z3,z4,z5]),(0,[z7,z0,z801,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z345]),(0,[z57,z7,z122,z58,z4,z5]),(0,[z530,z7,z2,z3,z4,z25]),(0,[z7,z121,z0,z3,z4,z25]),(0,[z7,z0,z3,z4,z81,z175]),(0,[z296,z0,z3,z4,z5,z481])],[(0,[z7,z64,z0,z480,z4,z5]),(0,[z802,z0,z2,z3,z4,z5]),(0,[z57,z416,z2,z58,z4,z5]),(0,[z7,z0,z431,z3,z4,z25]),(0,[z0,z342,z2,z3,z4,z36]),(0,[z7,z0,z3,z86,z4,z175])],[(0,[z1,z33,z3,z4,z5,z25]),(0,[z0,z1,z2,z3,z803,z4]),(0,[z0,z1,z106,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z125]),(0,[z7,z0,z84,z3,z4,z81]),(0,[z7,z804,z2,z3,z4,z5])],[(0,[z1,z2,z16,z3,z4,z25]),(0,[z102,z1,z2,z3,z4,z25]),(0,[z15,z0,z134,z3,z4,z5]),(0,[z7,z0,z2,z572,z85,z5]),(0,[z805,z0,z2,z3,z4,z5])],[(0,[z7,z0,z806,z3,z4,z5]),(0,[z7,z0,z2,z3,z238,z6])],[(0,[z7,z807,z2,z3,z4,z5]),(0,[z7,z0,z122,z3,z4,z5]),(0,[z7,z0,z808,z3,z4,z5]),(0,[z0,z2,z3,z4,z25,z379])],[(0,[z7,z0,z29,z3,z4,z25]),(0,[z325,z1,z2,z3,z4,z5]),(0,[z809,z0,z33,z3,z4,z5])],[(0,[z105,z1,z2,z3,z4,z25]),(0,[z7,z0,z22,z331,z3,z4]),(0,[z7,z2,z810,z58,z4,z5]),(0,[z530,z7,z2,z572,z4,z5])],[(0,[z1,z2,z3,z24,z4,z25]),(0,[z7,z543,z22,z3,z4,z5])],[(0,[z70,z743,z2,z3,z4,z5]),(0,[z15,z121,z0,z3,z4,z5]),(0,[z7,z0,z2,z811,z3,z4]),(0,[z7,z0,z812,z3,z4,z5]),(0,[z813,z0,z2,z3,z4,z5]),(0,[z814,z0,z2,z3,z4,z5]),(0,[z7,z0,z815,z3,z4,z5]),(0,[z7,z0,z816,z3,z4,z5]),(0,[z7,z0,z111,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z817]),(0,[z7,z0,z2,z3,z818,z5])]],
   [[(0,[z15,z0,z431,z3,z4,z5]),(0,[z17,z0,z53,z3,z4,z5]),(0,[z7,z0,z151,z3,z4,z5]),(0,[z7,z0,z155,z3,z4,z5])],[(0,[z70,z1,z2,z3,z4,z71]),(0,[z135,z1,z2,z3,z4,z25]),(0,[z7,z0,z49,z3,z4,z36]),(0,[z7,z0,z2,z810,z4,z5])],[(0,[z0,z2,z3,z4,z792,z5]),(0,[z7,z2,z3,z4,z36,z25]),(0,[z60,z0,z2,z3,z4,z36])],[(0,[z7,z0,z106,z3,z4,z177]),(0,[z7,z0,z33,z3,z4,z819]),(0,[z7,z0,z2,z3,z4,z166]),(0,[z7,z0,z820,z3,z4,z25]),(0,[z7,z0,z821,z3,z4,z5]),(0,[z7,z2,z110,z5,z67,z77])],[(0,[z1,z18,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z822]),(0,[z7,z0,z823,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z166]),(0,[z56,z7,z0,z3,z4,z34]),(0,[z7,z0,z2,z3,z4,z175])],[(0,[z47,z1,z2,z3,z4,z25]),(0,[z7,z0,z110,z5,z234,z77])],[(0,[z0,z1,z215,z3,z4,z5]),(0,[z7,z824,z0,z3,z4,z5]),(0,[z7,z405,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z825]),(0,[z7,z0,z2,z3,z826,z5])],[(0,[z0,z1,z168,z3,z4,z5]),(0,[z0,z543,z53,z3,z4,z5]),(0,[z7,z64,z0,z641,z4,z5])],[(0,[z1,z2,z3,z4,z81,z25]),(0,[z0,z827,z2,z3,z4,z5])],[(0,[z70,z1,z2,z3,z4,z36]),(0,[z1,z2,z3,z86,z4,z25]),(0,[z388,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z300,z4,z5]),(0,[z47,z0,z2,z299,z4,z5]),(0,[z7,z0,z575,z86,z4,z5]),(0,[z7,z0,z828,z3,z4,z5])],[(0,[z1,z2,z3,z4,z93,z25]),(0,[z7,z33,z3,z4,z5,z67]),(0,[z60,z0,z22,z3,z4,z5]),(0,[z7,z0,z132,z3,z4,z175]),(0,[z7,z0,z2,z3,z4,z829])],[(0,[z1,z2,z104,z3,z4,z25]),(0,[z7,z105,z33,z3,z4,z25]),(0,[z7,z22,z33,z3,z4,z25]),(0,[z95,z0,z65,z3,z4,z5]),(0,[z530,z7,z830,z3,z4,z5]),(0,[z7,z0,z831,z3,z4,z5])],[(0,[z530,z7,z2,z3,z237,z5]),(0,[z7,z0,z832,z3,z4,z5])],[(0,[z7,z0,z833,z3,z4,z5]),(0,[z7,z0,z834,z3,z4,z5]),(0,[z44,z0,z2,z3,z4,z520]),(0,[z7,z0,z835,z3,z4,z36])],[(0,[z330,z0,z2,z3,z4,z5]),(0,[z172,z0,z2,z3,z4,z36]),(0,[z14,z44,z2,z3,z237,z5]),(0,[z281,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z836])],[(0,[z1,z2,z110,z3,z4,z25]),(0,[z202,z0,z33,z3,z4,z93]),(0,[z7,z0,z22,z156,z4,z52]),(0,[z0,z2,z3,z4,z5,z837])]],
   [[(0,[z416,z0,z2,z3,z4,z5]),(0,[z7,z0,z549,z3,z4,z36])],[(0,[z0,z1,z134,z3,z4,z5]),(0,[z7,z838,z2,z3,z4,z5])],[(0,[z7,z703,z33,z3,z4,z5]),(0,[z7,z0,z839,z3,z4,z5]),(0,[z7,z595,z2,z3,z4,z36])],[(0,[z7,z0,z3,z91,z4,z25])],[(0,[z15,z22,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z840]),(0,[z7,z0,z22,z841,z4,z5]),(0,[z57,z7,z2,z58,z4,z5]),(0,[z7,z0,z2,z3,z4,z842]),(0,[z7,z0,z2,z843,z3,z4]),(0,[z7,z0,z331,z3,z4,z234]),(0,[z844,z0,z2,z3,z4,z5]),(0,[z0,z845,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z4,z71]),(0,[z15,z0,z2,z3,z4,z88]),(0,[z15,z0,z389,z3,z4,z5]),(0,[z281,z0,z2,z572,z4,z5]),(0,[z0,z422,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z846]),(0,[z0,z2,z110,z5,z379,z77])],[(0,[z7,z0,z2,z659,z5,z77])],[(0,[z7,z0,z22,z3,z547,z4]),(0,[z10,z293,z33,z3,z4,z5]),(0,[z7,z0,z847,z3,z4,z5]),(0,[z7,z33,z3,z4,z5,z143]),(0,[z7,z0,z2,z3,z4,z848])],[(0,[z15,z0,z54,z3,z4,z5]),(0,[z7,z0,z622,z3,z4,z25]),(0,[z7,z229,z389,z3,z4,z5]),(0,[z56,z7,z0,z3,z4,z217])],[(0,[z0,z1,z2,z849,z4,z5]),(0,[z7,z0,z850,z3,z4,z5]),(0,[z7,z0,z22,z110,z5,z77]),(0,[z7,z0,z2,z3,z851,z25]),(0,[z852,z0,z2,z3,z4,z5])],[(0,[z7,z0,z33,z3,z4,z5]),(0,[z7,z0,z853,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z854]),(0,[z7,z595,z22,z3,z4,z5]),(0,[z7,z0,z39,z3,z4,z313]),(0,[z7,z2,z3,z4,z5,z842]),(0,[z0,z855,z2,z3,z4,z5]),(0,[z0,z856,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z857,z4]),(0,[z7,z0,z3,z4,z5,z858]),(0,[z7,z0,z2,z3,z859,z4]),(0,[z0,z2,z3,z4,z860,z93]),(0,[z7,z861,z0,z3,z4,z5]),(0,[z862,z0,z2,z3,z4,z5])],[(0,[z70,z1,z2,z3,z4,z400]),(0,[z0,z863,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z25]),(0,[z7,z325,z33,z3,z4,z5]),(0,[z7,z0,z490,z3,z4,z25]),(0,[z864,z0,z2,z3,z4,z5])],[(0,[z7,z0,z165,z3,z4,z313])],[(0,[z865,z0,z2,z3,z4,z5]),(0,[z7,z0,z866,z3,z4,z5]),(0,[z7,z0,z284,z3,z4,z25])],[(0,[z7,z0,z375,z3,z4,z36]),(0,[z7,z0,z867,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z400]),(0,[z0,z342,z131,z3,z4,z5])]],
   [[(0,[z17,z0,z534,z3,z4,z5]),(0,[z589,z7,z0,z3,z4,z255]),(0,[z44,z0,z2,z3,z4,z25])],[(0,[z7,z0,z2,z3,z4,z150]),(0,[z704,z0,z53,z3,z4,z5]),(0,[z7,z251,z0,z456,z4,z5]),(0,[z7,z0,z3,z4,z36,z868])],[(0,[z76,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z869]),(0,[z7,z22,z3,z4,z36,z25])],[(0,[z1,z209,z2,z3,z4,z5]),(0,[z161,z0,z18,z3,z4,z5]),(0,[z7,z0,z22,z572,z4,z5]),(0,[z7,z0,z654,z3,z120,z5]),(0,[z7,z0,z870,z3,z4,z5]),(0,[z7,z0,z2,z3,z146,z701])],[(0,[z1,z2,z3,z4,z25,z6]),(0,[z7,z0,z2,z3,z4,z871]),(0,[z7,z0,z2,z3,z872,z5]),(0,[z7,z0,z3,z4,z263,z25]),(0,[z245,z0,z2,z3,z4,z36]),(0,[z530,z7,z873,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z267]),(0,[z0,z874,z2,z3,z4,z5])],[(0,[z7,z0,z875,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z876]),(0,[z7,z0,z877,z3,z4,z5])],[(0,[z1,z23,z2,z3,z4,z25]),(0,[z15,z0,z439,z3,z4,z5]),(0,[z7,z0,z878,z3,z4,z5]),(0,[z44,z0,z2,z572,z4,z5])],[(0,[z302,z0,z2,z3,z4,z5]),(0,[z879,z7,z0,z3,z4,z5])],[(0,[z1,z2,z3,z4,z25,z34]),(0,[z15,z0,z880,z3,z4,z5]),(0,[z15,z0,z22,z3,z4,z36]),(0,[z46,z0,z2,z3,z4,z93]),(0,[z162,z0,z397,z3,z4,z5]),(0,[z7,z0,z3,z881,z4,z5]),(0,[z302,z0,z33,z3,z4,z5]),(0,[z7,z102,z0,z3,z670,z5])],[(0,[z219,z0,z283,z3,z115,z5]),(0,[z7,z0,z2,z3,z882,z5]),(0,[z7,z0,z2,z3,z4,z883])],[(0,[z0,z743,z2,z3,z4,z5]),(0,[z10,z1,z33,z3,z4,z5]),(0,[z15,z0,z884,z3,z4,z5]),(0,[z15,z380,z0,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z796]),(0,[z7,z0,z885,z3,z4,z5])],[(0,[z1,z2,z563,z3,z4,z25]),(0,[z7,z0,z3,z94,z137,z5]),(0,[z219,z0,z2,z3,z792,z5]),(0,[z219,z0,z22,z3,z115,z5]),(0,[z245,z0,z22,z3,z4,z5]),(0,[z7,z388,z0,z3,z4,z36]),(0,[z7,z102,z0,z3,z4,z175])],[(0,[z0,z1,z2,z3,z4,z71]),(0,[z0,z1,z2,z3,z4,z88]),(0,[z0,z1,z389,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z35])],[(0,[z15,z506,z2,z3,z4,z5]),(0,[z162,z0,z18,z3,z4,z36]),(0,[z219,z0,z284,z3,z115,z5]),(0,[z95,z0,z2,z3,z4,z25])],[(0,[z7,z587,z22,z3,z4,z5]),(0,[z7,z0,z886,z3,z4,z5]),(0,[z7,z0,z887,z3,z4,z5])]],
   [[(0,[z15,z0,z2,z3,z4,z400]),(0,[z57,z1,z2,z3,z4,z25]),(0,[z0,z1,z54,z3,z4,z5]),(0,[z416,z0,z2,z3,z4,z345]),(0,[z7,z0,z2,z3,z4,z888]),(0,[z388,z0,z3,z4,z5,z267])],[(0,[z0,z773,z53,z3,z4,z5]),(0,[z7,z0,z2,z889,z3,z4]),(0,[z7,z0,z2,z890,z4,z5])],[(0,[z7,z0,z375,z3,z4,z400]),(0,[z7,z0,z269,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z891]),(0,[z7,z0,z2,z3,z4,z892])],[(0,[z15,z0,z2,z3,z4,z508]),(0,[z7,z0,z549,z332,z4,z5]),(0,[z7,z0,z2,z3,z4,z893])],[(0,[z70,z1,z29,z3,z4,z5]),(0,[z492,z0,z2,z3,z4,z5]),(0,[z57,z7,z2,z58,z4,z345]),(0,[z220,z0,z168,z3,z4,z5]),(0,[z7,z0,z620,z3,z4,z255]),(0,[z894,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z331,z3,z4]),(0,[z7,z0,z895,z3,z4,z5])],[(0,[z7,z0,z2,z896,z3,z4]),(0,[z202,z0,z49,z3,z4,z93]),(0,[z7,z0,z22,z3,z4,z285]),(0,[z416,z0,z122,z3,z4,z5]),(0,[z7,z0,z68,z384,z3,z4])],[(0,[z7,z897,z0,z3,z4,z5]),(0,[z7,z102,z0,z3,z139,z5]),(0,[z898,z2,z3,z4,z5,z67])],[(0,[z1,z2,z3,z4,z25,z280]),(0,[z7,z899,z2,z3,z4,z5]),(0,[z7,z0,z155,z110,z5,z77])],[(0,[z7,z0,z2,z3,z4,z900]),(0,[z0,z1,z3,z4,z5,z901]),(0,[z475,z1,z2,z3,z4,z5]),(0,[z7,z0,z902,z3,z4,z5]),(0,[z392,z0,z2,z361,z4,z5]),(0,[z7,z0,z2,z3,z4,z903]),(0,[z7,z0,z3,z4,z5,z904]),(0,[z7,z64,z0,z86,z4,z25]),(0,[z7,z160,z0,z3,z4,z255])],[(0,[z7,z905,z0,z3,z4,z5]),(0,[z15,z0,z3,z4,z5,z263]),(0,[z0,z906,z2,z3,z4,z5])],[(0,[z202,z0,z2,z3,z4,z401]),(0,[z17,z0,z53,z3,z4,z25]),(0,[z7,z0,z33,z3,z4,z345]),(0,[z7,z0,z39,z3,z4,z25]),(0,[z7,z0,z3,z907,z4,z5]),(0,[z7,z0,z155,z3,z4,z25]),(0,[z7,z2,z3,z4,z25,z108]),(0,[z7,z0,z2,z3,z4,z908]),(0,[z0,z909,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z910]),(0,[z7,z0,z2,z3,z4,z911]),(0,[z7,z0,z912,z3,z4,z5]),(0,[z7,z0,z156,z4,z481,z52])],[(0,[z7,z0,z913,z3,z4,z5]),(0,[z47,z228,z2,z3,z4,z5]),(0,[z7,z0,z914,z3,z4,z5]),(0,[z7,z118,z22,z3,z4,z25]),(0,[z7,z0,z131,z3,z4,z25])],[(0,[z1,z2,z3,z4,z120,z25]),(0,[z7,z0,z3,z4,z5,z915]),(0,[z7,z0,z165,z3,z4,z25]),(0,[z7,z102,z0,z3,z120,z25]),(0,[z7,z0,z2,z110,z751,z5])],[(0,[z0,z283,z73,z3,z4,z5]),(0,[z281,z0,z2,z3,z4,z520]),(0,[z7,z2,z3,z716,z237,z5])],[(0,[z0,z1,z439,z3,z4,z5]),(0,[z145,z1,z2,z3,z4,z25]),(0,[z309,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z916]),(0,[z7,z0,z3,z547,z300,z4]),(0,[z7,z501,z0,z3,z120,z5]),(0,[z7,z0,z22,z3,z4,z313])]],
   [[(0,[z7,z0,z917,z3,z4,z5]),(0,[z530,z1,z2,z3,z4,z5]),(0,[z15,z0,z2,z332,z4,z5]),(0,[z492,z0,z22,z3,z4,z5]),(0,[z7,z824,z0,z3,z4,z25]),(0,[z7,z2,z3,z4,z36,z67])],[(0,[z60,z0,z2,z3,z4,z5]),(0,[z0,z1,z22,z3,z4,z36]),(0,[z918,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z919]),(0,[z0,z342,z22,z3,z4,z5]),(0,[z920,z0,z2,z3,z4,z5]),(0,[z530,z7,z3,z4,z5,z234])],[(0,[z7,z0,z3,z4,z5,z921]),(0,[z7,z0,z3,z4,z5,z922])],[(0,[z7,z0,z923,z3,z4,z5]),(0,[z47,z0,z2,z48,z4,z36]),(0,[z7,z0,z2,z572,z4,z166])],[(0,[z15,z0,z131,z3,z4,z5]),(0,[z7,z246,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z924]),(0,[z7,z550,z22,z3,z4,z5]),(0,[z0,z22,z3,z4,z5,z267]),(0,[z7,z0,z3,z4,z5,z925]),(0,[z926,z7,z0,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z324]),(0,[z294,z7,z0,z3,z4,z255]),(0,[z7,z0,z3,z4,z5,z927]),(0,[z7,z0,z2,z156,z4,z52])],[(0,[z7,z228,z389,z3,z4,z5]),(0,[z928,z0,z2,z3,z4,z5])],[(0,[z15,z0,z29,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z400]),(0,[z7,z0,z33,z3,z4,z175]),(0,[z929,z0,z2,z3,z4,z5]),(0,[z7,z0,z3,z4,z36,z234])],[(0,[z7,z0,z2,z3,z4,z930]),(0,[z1,z2,z3,z30,z4,z25]),(0,[z7,z0,z931,z3,z4,z5]),(0,[z7,z932,z0,z3,z4,z5]),(0,[z7,z33,z3,z4,z318,z5]),(0,[z7,z0,z2,z3,z4,z933]),(0,[z7,z0,z2,z3,z4,z934])],[(0,[z676,z0,z53,z3,z4,z5]),(0,[z7,z0,z935,z3,z4,z5]),(0,[z936,z7,z0,z3,z4,z5]),(0,[z937,z0,z2,z3,z4,z5])],[(0,[z1,z33,z3,z85,z4,z5]),(0,[z7,z0,z2,z841,z4,z5]),(0,[z7,z703,z2,z3,z4,z25]),(0,[z7,z0,z938,z3,z4,z5]),(0,[z7,z0,z2,z3,z376,z36])],[(0,[z47,z0,z22,z48,z4,z5]),(0,[z7,z229,z939,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z520]),(0,[z309,z0,z2,z3,z4,z148])],[(0,[z281,z0,z549,z3,z4,z5])],[(0,[z7,z0,z940,z3,z4,z5]),(0,[z7,z0,z2,z3,z547,z4])],[(0,[z7,z2,z331,z3,z4,z67]),(0,[z7,z0,z941,z3,z4,z5])]],
   [[(0,[z7,z0,z65,z3,z4,z345]),(0,[z7,z0,z942,z3,z4,z5]),(0,[z7,z0,z3,z4,z943,z255]),(0,[z7,z0,z2,z110,z5,z77]),(0,[z530,z944,z2,z3,z4,z5])],[(0,[z1,z2,z348,z3,z4,z25]),(0,[z0,z1,z3,z4,z5,z263]),(0,[z7,z2,z3,z4,z38,z25]),(0,[z7,z0,z2,z945,z4,z5]),(0,[z7,z0,z946,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z947]),(0,[z7,z0,z2,z3,z4,z948]),(0,[z7,z0,z3,z4,z5,z949]),(0,[z7,z0,z2,z3,z406,z36])],[(0,[z17,z0,z773,z3,z4,z5]),(0,[z7,z0,z950,z3,z4,z5]),(0,[z330,z0,z33,z3,z4,z5]),(0,[z0,z22,z82,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z951]),(0,[z952,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z25]),(0,[z7,z0,z953,z3,z4,z5]),(0,[z7,z0,z39,z3,z4,z285]),(0,[z7,z0,z358,z3,z4,z36])],[(0,[z70,z1,z22,z3,z4,z5]),(0,[z416,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z954,z5]),(0,[z7,z0,z221,z3,z4,z36])],[(0,[z7,z0,z955,z3,z4,z5])],[(0,[z7,z0,z18,z3,z4,z175]),(0,[z956,z0,z2,z3,z4,z5]),(0,[z7,z0,z165,z3,z4,z285])],[(0,[z17,z0,z420,z3,z4,z5]),(0,[z7,z0,z3,z4,z957,z5]),(0,[z958,z0,z2,z3,z4,z5])],[(0,[z7,z0,z959,z3,z4,z5]),(0,[z0,z1,z2,z332,z4,z5]),(0,[z112,z1,z2,z3,z4,z25]),(0,[z474,z1,z2,z3,z4,z5]),(0,[z188,z15,z2,z3,z4,z25]),(0,[z57,z7,z33,z58,z4,z5])],[(0,[z7,z0,z2,z3,z4,z960]),(0,[z172,z0,z22,z3,z4,z5]),(0,[z7,z33,z3,z359,z4,z5]),(0,[z121,z0,z3,z4,z5,z379])],[(0,[z1,z2,z33,z3,z4,z25]),(0,[z7,z961,z2,z3,z4,z5]),(0,[z7,z0,z962,z3,z4,z5]),(0,[z7,z0,z2,z572,z4,z5]),(0,[z7,z2,z89,z3,z4,z25])],[(0,[z0,z1,z431,z3,z4,z5]),(0,[z7,z0,z2,z963,z4,z5]),(0,[z7,z0,z2,z3,z964,z5])],[(0,[z219,z0,z2,z32,z3,z115]),(0,[z965,z0,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z842,z25]),(0,[z7,z0,z966,z3,z4,z5])],[(0,[z47,z0,z2,z361,z4,z5]),(0,[z7,z0,z283,z3,z4,z25]),(0,[z7,z0,z384,z3,z4,z36]),(0,[z7,z967,z2,z3,z4,z5])],[(0,[z118,z1,z2,z3,z4,z25]),(0,[z7,z0,z110,z111,z5,z77]),(0,[z7,z0,z3,z968,z4,z5]),(0,[z7,z969,z0,z3,z4,z5])],[(0,[z15,z0,z970,z3,z4,z5]),(0,[z15,z0,z3,z91,z4,z5]),(0,[z7,z114,z2,z3,z4,z25]),(0,[z7,z0,z971,z3,z4,z5]),(0,[z7,z2,z3,z4,z36,z213]),(0,[z44,z0,z549,z3,z4,z5]),(0,[z7,z336,z2,z3,z4,z25])]],
   [[(0,[z15,z0,z2,z3,z4,z36]),(0,[z0,z1,z29,z3,z4,z5]),(0,[z7,z0,z22,z3,z972,z5])],[(0,[z0,z1,z973,z3,z4,z5]),(0,[z15,z0,z33,z3,z4,z36]),(0,[z7,z0,z974,z3,z4,z5]),(0,[z7,z596,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z975])],[(0,[z7,z105,z269,z3,z4,z25]),(0,[z272,z0,z53,z3,z4,z5]),(0,[z302,z0,z2,z3,z4,z25]),(0,[z188,z7,z2,z3,z4,z842])],[(0,[z14,z15,z2,z3,z237,z5]),(0,[z245,z0,z2,z3,z4,z5]),(0,[z219,z0,z2,z3,z115,z5]),(0,[z7,z0,z2,z3,z4,z976]),(0,[z7,z0,z2,z769,z3,z25]),(0,[z7,z0,z3,z977,z120,z5]),(0,[z7,z0,z2,z4,z751,z5])],[(0,[z10,z1,z2,z3,z4,z25]),(0,[z15,z0,z622,z3,z4,z5]),(0,[z7,z0,z978,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z401]),(0,[z7,z0,z33,z3,z4,z150]),(0,[z95,z0,z2,z3,z376,z5]),(0,[z0,z2,z3,z4,z124,z379]),(0,[z7,z121,z0,z3,z4,z124])],[(0,[z0,z1,z3,z979,z4,z5]),(0,[z98,z1,z2,z3,z4,z25]),(0,[z76,z0,z33,z3,z4,z5])],[(0,[z600,z0,z2,z3,z362,z5]),(0,[z7,z0,z2,z980,z3,z4]),(0,[z7,z228,z981,z3,z4,z5]),(0,[z7,z2,z154,z3,z4,z25])],[(0,[z15,z0,z22,z3,z4,z5]),(0,[z15,z0,z490,z3,z4,z5]),(0,[z7,z982,z2,z3,z4,z5]),(0,[z7,z0,z830,z3,z4,z5])],[(0,[z0,z49,z73,z3,z4,z5]),(0,[z983,z0,z2,z3,z4,z5]),(0,[z7,z0,z358,z3,z4,z508]),(0,[z7,z0,z984,z3,z4,z5])],[(0,[z15,z0,z284,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z985]),(0,[z7,z0,z22,z3,z4,z11]),(0,[z7,z22,z209,z3,z4,z5]),(0,[z416,z0,z65,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z986]),(0,[z7,z0,z2,z3,z146,z306]),(0,[z7,z0,z987,z3,z4,z5])],[(0,[z7,z0,z988,z3,z4,z5]),(0,[z95,z0,z2,z3,z406,z5]),(0,[z7,z388,z0,z3,z4,z5]),(0,[z56,z7,z0,z3,z4,z175])],[(0,[z7,z0,z989,z3,z4,z5]),(0,[z7,z0,z49,z68,z3,z4]),(0,[z7,z0,z2,z3,z4,z285])],[(0,[z1,z2,z3,z4,z266,z25]),(0,[z1,z2,z3,z424,z4,z5]),(0,[z7,z0,z2,z3,z4,z990]),(0,[z7,z0,z2,z3,z4,z991]),(0,[z7,z0,z992,z3,z4,z5])],[(0,[z172,z0,z2,z3,z4,z125]),(0,[z7,z417,z22,z3,z4,z5]),(0,[z57,z7,z65,z58,z4,z5])],[(0,[z0,z1,z993,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z994]),(0,[z15,z0,z995,z3,z4,z5]),(0,[z15,z0,z2,z32,z3,z4]),(0,[z7,z0,z996,z3,z4,z5]),(0,[z7,z0,z84,z3,z4,z25]),(0,[z7,z0,z3,z4,z5,z481])]],
   [[(0,[z1,z2,z3,z4,z25,z77]),(0,[z7,z0,z2,z997,z3,z4]),(0,[z7,z0,z3,z4,z5,z998]),(0,[z7,z0,z2,z377,z4,z314])],[(0,[z1,z2,z3,z4,z36,z25])],[(0,[z7,z0,z3,z999,z4,z5])],[(0,[z7,z0,z1000,z3,z4,z5]),(0,[z7,z0,z65,z3,z4,z5]),(0,[z7,z64,z0,z41,z4,z5]),(0,[z7,z0,z2,z3,z4,z1001])],[(0,[z7,z0,z1002,z3,z4,z5]),(0,[z7,z0,z566,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1003]),(0,[z46,z0,z2,z3,z4,z310]),(0,[z7,z0,z1004,z3,z4,z5])],[],[(0,[z117,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z313]),(0,[z530,z7,z2,z3,z406,z5]),(0,[z1005,z0,z2,z3,z4,z5])],[(0,[z0,z1,z3,z91,z4,z5]),(0,[z170,z0,z53,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z313]),(0,[z14,z7,z439,z3,z237,z5])],[(0,[z0,z1,z2,z3,z4,z36]),(0,[z1006,z15,z0,z3,z4,z5]),(0,[z15,z0,z84,z3,z4,z5]),(0,[z7,z0,z2,z1007,z4,z5]),(0,[z7,z0,z212,z86,z4,z5]),(0,[z7,z0,z1008,z3,z4,z5]),(0,[z7,z0,z1009,z3,z4,z5]),(0,[z7,z0,z1010,z3,z4,z5]),(1,[z228,z2,z3,z4,z93]),(0,[z7,z1011,z0,z3,z4,z5]),(0,[z492,z0,z33,z3,z4,z5]),(0,[z7,z0,z33,z331,z3,z4]),(0,[z1012,z0,z2,z3,z4,z5]),(0,[z7,z0,z122,z3,z4,z25]),(0,[z7,z0,z3,z4,z5,z868])],[(0,[z1013,z0,z2,z3,z4,z5]),(0,[z78,z1,z2,z3,z4,z5]),(0,[z0,z342,z2,z3,z4,z5]),(0,[z586,z7,z2,z3,z4,z25])],[(0,[z1,z2,z3,z8,z4,z25]),(0,[z7,z762,z2,z3,z4,z5]),(0,[z530,z7,z2,z3,z4,z1014])],[(0,[z57,z95,z2,z58,z4,z5]),(0,[z7,z1015,z0,z3,z4,z5]),(0,[z7,z0,z282,z3,z4,z81])],[(0,[z0,z1,z622,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1016]),(0,[z7,z228,z2,z3,z4,z93]),(0,[z530,z7,z2,z189,z4,z5]),(0,[z7,z0,z549,z3,z4,z166]),(0,[z7,z0,z111,z3,z4,z25])],[(0,[z1,z2,z3,z4,z38,z25]),(0,[z0,z1,z2,z3,z851,z5]),(0,[z99,z1,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z125]),(0,[z7,z0,z151,z3,z4,z25]),(0,[z7,z0,z2,z3,z1017,z4]),(0,[z0,z906,z33,z3,z4,z5]),(0,[z7,z657,z2,z3,z4,z25])],[(0,[z7,z246,z2,z3,z4,z25]),(0,[z0,z1018,z2,z3,z4,z5])],[(0,[z7,z0,z1019,z3,z4,z5]),(0,[z7,z33,z189,z3,z4,z25]),(0,[z7,z0,z2,z3,z1020,z5]),(0,[z0,z2,z3,z4,z25,z267])]],
   [[(0,[z0,z1,z22,z3,z4,z5]),(0,[z0,z1,z490,z3,z4,z5]),(0,[z76,z0,z2,z331,z3,z4])],[(0,[z7,z0,z2,z3,z4,z1021]),(0,[z15,z0,z122,z3,z4,z5]),(0,[z7,z648,z33,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z119]),(0,[z7,z0,z873,z3,z4,z5])],[(0,[z0,z1,z284,z3,z4,z5]),(0,[z1,z2,z3,z4,z96,z25]),(0,[z7,z1022,z2,z3,z4,z5]),(0,[z7,z0,z3,z1023,z4,z5])],[(0,[z7,z0,z49,z3,z4,z5]),(0,[z47,z0,z2,z48,z4,z5]),(0,[z7,z0,z1024,z3,z4,z5]),(0,[z7,z0,z2,z3,z146,z55]),(0,[z7,z0,z2,z3,z4,z520])],[(0,[z15,z64,z0,z86,z4,z5]),(0,[z7,z0,z2,z3,z1025,z4]),(0,[z0,z2,z798,z48,z4,z5]),(0,[z1026,z0,z2,z3,z4,z5]),(0,[z7,z0,z1027,z3,z4,z5])],[(0,[z60,z0,z33,z3,z4,z5]),(0,[z186,z0,z2,z3,z4,z36])],[(0,[z15,z0,z3,z1028,z4,z5]),(0,[z15,z0,z39,z3,z4,z5]),(0,[z15,z0,z155,z3,z4,z5]),(0,[z15,z0,z151,z3,z4,z5]),(0,[z7,z0,z1029,z3,z4,z5]),(0,[z1030,z0,z2,z3,z4,z5]),(0,[z7,z0,z1031,z3,z4,z5])],[(0,[z0,z1,z2,z32,z3,z4]),(0,[z7,z0,z1032,z3,z4,z5])],[(0,[z0,z1,z2,z1033,z4,z5])],[(0,[z15,z0,z165,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z166]),(0,[z15,z102,z0,z3,z120,z5]),(0,[z7,z0,z1034,z3,z4,z5])],[(0,[z7,z0,z33,z156,z4,z52])],[(0,[z70,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z115,z25]),(0,[z7,z0,z22,z3,z4,z177]),(0,[z7,z0,z1035,z3,z4,z5]),(0,[z330,z0,z2,z3,z4,z25]),(0,[z7,z0,z3,z4,z5,z791])],[(0,[z7,z0,z1036,z3,z4,z5]),(0,[z138,z0,z563,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1037])],[(0,[z135,z0,z157,z3,z4,z5]),(0,[z7,z0,z1038,z3,z4,z5]),(0,[z416,z0,z2,z3,z4,z25])],[(0,[z0,z1,z2,z3,z4,z508]),(0,[z14,z7,z2,z3,z716,z5]),(0,[z1039,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1040])],[(0,[z7,z0,z1041,z3,z4,z5]),(0,[z7,z2,z189,z85,z5,z77]),(0,[z7,z0,z835,z3,z4,z5]),(0,[z7,z0,z2,z3,z818,z4])]],
   [[(0,[z172,z0,z2,z3,z4,z5]),(0,[z1,z2,z27,z3,z4,z25]),(0,[z1042,z0,z2,z3,z4,z5]),(0,[z14,z7,z2,z332,z237,z5])],[(0,[z1,z2,z3,z146,z4,z25]),(0,[z7,z0,z1043,z3,z4,z5]),(0,[z7,z0,z2,z1044,z4,z5]),(0,[z7,z551,z33,z3,z4,z5]),(0,[z57,z7,z2,z58,z4,z25])],[(0,[z7,z0,z33,z3,z547,z4]),(0,[z7,z228,z2,z3,z4,z36]),(0,[z7,z0,z549,z3,z4,z5]),(0,[z7,z0,z1045,z3,z4,z5])],[(0,[z7,z591,z2,z3,z4,z25]),(0,[z7,z0,z221,z3,z4,z5]),(0,[z1046,z0,z22,z3,z4,z5]),(1,[z330,z2,z3,z4,z25]),(0,[z7,z0,z2,z1047,z3,z4])],[(0,[z0,z1,z3,z1048,z4,z5]),(0,[z7,z0,z33,z110,z5,z77]),(0,[z7,z0,z84,z3,z4,z255])],[(0,[z0,z1,z2,z3,z4,z125]),(0,[z7,z0,z1049,z3,z4,z5]),(0,[z7,z0,z2,z3,z1050,z4]),(0,[z0,z249,z2,z3,z4,z36]),(0,[z1051,z0,z2,z3,z4,z5])],[(0,[z56,z15,z0,z3,z4,z255]),(0,[z7,z0,z2,z3,z4,z1052]),(0,[z7,z0,z3,z4,z5,z1053]),(0,[z7,z33,z3,z4,z510,z5]),(0,[z7,z0,z22,z3,z376,z5]),(0,[z7,z2,z3,z4,z1054,z67]),(0,[z0,z1055,z2,z3,z4,z5])],[(0,[z15,z703,z2,z3,z4,z5]),(0,[z202,z229,z2,z3,z4,z93]),(0,[z7,z0,z33,z3,z4,z25]),(0,[z7,z0,z2,z3,z972,z5]),(0,[z0,z422,z358,z3,z4,z5]),(0,[z7,z330,z2,z3,z4,z25]),(0,[z7,z2,z320,z3,z4,z36])],[(0,[z216,z7,z2,z3,z4,z25]),(0,[z46,z0,z2,z3,z4,z401]),(0,[z0,z2,z3,z798,z4,z5]),(0,[z7,z0,z2,z3,z4,z1056]),(0,[z7,z599,z33,z3,z4,z5]),(0,[z7,z2,z3,z4,z310,z25]),(0,[z1057,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1058])],[(0,[z7,z0,z1059,z3,z4,z5])],[(0,[z17,z0,z563,z3,z4,z5])],[(0,[z198,z1,z33,z3,z4,z5]),(0,[z7,z0,z1060,z3,z4,z5]),(0,[z1061,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1062]),(0,[z7,z0,z22,z3,z406,z5]),(0,[z330,z61,z2,z3,z4,z5]),(0,[z76,z0,z2,z110,z5,z77])],[(0,[z0,z249,z22,z3,z4,z5]),(0,[z7,z0,z1063,z3,z4,z5])],[(0,[z0,z1,z39,z3,z4,z5]),(0,[z0,z1,z155,z3,z4,z5]),(0,[z7,z0,z33,z572,z4,z5]),(0,[z7,z0,z279,z3,z4,z36]),(0,[z0,z1064,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z4,z5]),(0,[z1,z2,z3,z28,z4,z25]),(0,[z1065,z0,z2,z3,z4,z5]),(0,[z76,z0,z2,z3,z4,z25]),(0,[z7,z0,z3,z4,z5,z234])]],
   [[(0,[z0,z1,z131,z3,z4,z5]),(0,[z7,z0,z2,z3,z1066,z4])],[(0,[z7,z0,z375,z3,z4,z5]),(0,[z0,z1,z165,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z166]),(0,[z7,z0,z2,z3,z4,z11]),(0,[z530,z7,z2,z58,z4,z5])],[(0,[z7,z0,z1067,z3,z4,z5]),(1,[z1,z22,z3,z4,z25])],[(0,[z7,z0,z2,z1068,z3,z5]),(0,[z7,z0,z1069,z3,z4,z5]),(0,[z7,z0,z215,z3,z4,z36]),(0,[z0,z1070,z2,z3,z4,z5])],[(0,[z7,z0,z2,z1071,z3,z4]),(0,[z7,z228,z2,z3,z4,z74]),(0,[z7,z0,z1072,z3,z4,z5]),(0,[z1073,z0,z2,z3,z4,z5]),(0,[z7,z0,z168,z3,z4,z36])],[(0,[z220,z0,z2,z3,z4,z36]),(0,[z7,z0,z358,z3,z4,z35]),(0,[z7,z0,z2,z1074,z3,z4])],[(0,[z7,z1,z22,z3,z4,z25]),(0,[z7,z0,z3,z300,z4,z36])],[(0,[z15,z1,z2,z3,z4,z36]),(0,[z202,z0,z2,z3,z4,z624]),(0,[z219,z0,z33,z3,z115,z5]),(0,[z245,z0,z33,z3,z4,z5])],[(0,[z7,z0,z885,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z1075]),(0,[z530,z7,z2,z3,z4,z124]),(0,[z7,z0,z3,z1076,z4,z5])],[(0,[z15,z0,z283,z3,z4,z5]),(0,[z7,z0,z2,z3,z1077,z5]),(0,[z7,z0,z1078,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1079])],[(0,[z7,z0,z1080,z3,z4,z5]),(0,[z0,z246,z18,z3,z4,z5]),(0,[z7,z0,z3,z4,z81,z247]),(0,[z7,z0,z2,z1081,z4,z5]),(0,[z7,z0,z2,z3,z4,z1082]),(0,[z7,z0,z2,z3,z376,z345]),(0,[z7,z0,z2,z572,z237,z5]),(0,[z7,z0,z2,z110,z25,z77]),(0,[z7,z0,z2,z3,z4,z1083]),(0,[z7,z0,z1084,z3,z4,z5])],[(0,[z7,z0,z1085,z3,z4,z5]),(0,[z15,z114,z2,z3,z4,z5]),(0,[z7,z0,z1086,z3,z4,z5]),(0,[z7,z10,z33,z3,z4,z36]),(0,[z294,z7,z0,z3,z4,z436]),(0,[z186,z0,z39,z3,z4,z5]),(0,[z7,z0,z1087,z3,z4,z5]),(0,[z7,z0,z3,z1088,z4,z5])],[(0,[z216,z0,z2,z3,z4,z148]),(0,[z219,z0,z2,z3,z362,z5]),(0,[z7,z0,z1089,z3,z4,z5]),(0,[z330,z0,z566,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1090])],[(0,[z7,z1091,z2,z3,z4,z5]),(0,[z7,z0,z1092,z3,z4,z5]),(0,[z188,z7,z22,z3,z4,z25]),(0,[z7,z0,z65,z3,z4,z25]),(0,[z1093,z0,z2,z3,z4,z5]),(0,[z7,z0,z1094,z3,z4,z5])],[(0,[z228,z1,z2,z3,z4,z5]),(0,[z7,z229,z22,z3,z4,z5]),(0,[z186,z0,z165,z3,z4,z5]),(0,[z7,z0,z134,z3,z4,z36])],[(0,[z7,z0,z2,z3,z4,z1095]),(0,[z7,z0,z1096,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1097]),(0,[z7,z0,z122,z3,z376,z5])]],
   [[(0,[z162,z0,z18,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z285]),(0,[z7,z0,z2,z3,z406,z345]),(0,[z14,z7,z2,z3,z237,z36])],[(0,[z1098,z0,z2,z3,z4,z5]),(0,[z492,z0,z2,z3,z4,z25]),(0,[z7,z0,z3,z1099,z4,z5])],[(0,[z15,z0,z2,z3,z4,z35]),(0,[z7,z543,z2,z3,z4,z25]),(0,[z7,z0,z49,z3,z146,z4]),(0,[z667,z7,z0,z3,z4,z255]),(0,[z0,z1100,z2,z3,z4,z5])],[(0,[z7,z0,z1101,z3,z4,z5]),(0,[z1,z2,z3,z171,z4,z25]),(0,[z0,z2,z3,z4,z860,z5]),(0,[z7,z0,z1102,z3,z4,z5]),(0,[z7,z10,z762,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1103])],[(0,[z7,z0,z269,z3,z4,z5]),(0,[z7,z0,z595,z3,z4,z255]),(0,[z7,z121,z3,z4,z5,z67])],[(0,[z7,z0,z1104,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1105]),(0,[z117,z0,z2,z3,z4,z5]),(0,[z7,z0,z122,z3,z406,z5])],[(0,[z121,z0,z1,z3,z4,z5]),(0,[z7,z1106,z2,z3,z4,z5]),(0,[z7,z0,z1107,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z202,z0,z2,z3,z4,z148])],[(0,[z1,z2,z292,z3,z4,z25]),(0,[z7,z0,z3,z4,z5,z1108]),(0,[z7,z0,z2,z3,z4,z119]),(0,[z14,z7,z22,z3,z237,z5]),(0,[z7,z0,z2,z1109,z3,z4])],[(0,[z7,z0,z1110,z3,z4,z5]),(0,[z1111,z0,z2,z3,z4,z5]),(0,[z7,z0,z1112,z3,z4,z5])],[(0,[z7,z648,z2,z3,z4,z25]),(0,[z7,z0,z168,z3,z4,z508])],[(0,[z381,z15,z0,z3,z4,z5]),(0,[z0,z249,z39,z3,z4,z5]),(0,[z220,z0,z2,z3,z4,z508]),(0,[z0,z82,z23,z3,z4,z5]),(0,[z7,z0,z1113,z3,z4,z5])],[(0,[z0,z1,z33,z3,z4,z36]),(0,[z309,z1,z2,z3,z4,z25]),(0,[z7,z0,z269,z3,z4,z150]),(0,[z7,z0,z439,z332,z4,z5]),(0,[z7,z0,z2,z3,z4,z1114]),(0,[z1115,z0,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z994,z67])],[(0,[z145,z0,z2,z48,z4,z5]),(0,[z7,z0,z1116,z3,z4,z5]),(0,[z7,z1117,z0,z3,z4,z5]),(0,[z0,z342,z33,z3,z4,z5])],[(0,[z7,z0,z1118,z3,z4,z5]),(0,[z7,z0,z2,z1119,z3,z4]),(0,[z7,z762,z33,z3,z4,z5]),(0,[z0,z249,z165,z3,z4,z5]),(0,[z60,z0,z2,z3,z4,z25])],[(0,[z15,z905,z0,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z345]),(0,[z257,z0,z18,z3,z4,z5]),(0,[z7,z1120,z2,z3,z4,z5]),(0,[z47,z0,z2,z690,z4,z5]),(0,[z589,z7,z0,z3,z4,z34]),(0,[z920,z0,z2,z3,z4,z25])]],
   [[(0,[z7,z0,z1121,z3,z4,z5]),(0,[z1013,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1122]),(0,[z7,z0,z2,z3,z1123,z5]),(0,[z7,z0,z1124,z3,z4,z5])],[(0,[z0,z1,z283,z3,z4,z5]),(0,[z117,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z943])],[(0,[z7,z0,z2,z3,z4,z177]),(0,[z109,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z1125,z4,z5]),(0,[z7,z0,z1126,z3,z4,z5])],[(0,[z586,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1127]),(0,[z7,z0,z1128,z3,z4,z5])],[(0,[z7,z64,z0,z435,z4,z5])],[(0,[z129,z1,z2,z3,z4,z5]),(0,[z381,z7,z0,z3,z4,z36]),(0,[z7,z1129,z2,z3,z4,z5]),(0,[z7,z1130,z0,z3,z4,z5])],[(0,[z61,z1,z131,z3,z4,z5]),(0,[z7,z0,z2,z1131,z4,z5]),(0,[z202,z228,z2,z3,z4,z93])],[(0,[z47,z0,z33,z48,z4,z5]),(0,[z7,z0,z33,z3,z4,z520]),(0,[z7,z1132,z0,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z1133]),(0,[z302,z0,z2,z3,z4,z119]),(0,[z0,z2,z3,z4,z5,z1134])],[(0,[z1,z2,z3,z4,z5,z25]),(0,[z15,z0,z111,z3,z4,z5]),(0,[z7,z10,z33,z3,z4,z125]),(0,[z57,z7,z2,z58,z376,z5]),(0,[z7,z0,z1135,z3,z4,z5]),(0,[z7,z0,z1136,z3,z4,z5])],[(0,[z13,z0,z2,z3,z185,z5]),(0,[z7,z0,z1137,z3,z4,z5]),(0,[z7,z0,z3,z4,z25,z481])],[(0,[z0,z1,z2,z3,z4,z35]),(0,[z7,z0,z2,z1138,z4,z5]),(0,[z15,z246,z2,z3,z4,z5]),(0,[z7,z0,z389,z3,z4,z36]),(0,[z7,z0,z22,z3,z4,z159]),(0,[z1046,z0,z2,z3,z4,z5]),(0,[z7,z0,z3,z4,z25,z998]),(0,[z7,z0,z2,z3,z4,z1139]),(0,[z1140,z7,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z237,z25]),(0,[z60,z1,z2,z3,z4,z5]),(0,[z15,z2,z3,z4,z36,z25]),(0,[z7,z0,z1141,z3,z4,z5]),(0,[z7,z0,z2,z3,z146,z75]),(0,[z1142,z0,z2,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z1143])],[(0,[z1144,z0,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z4,z175]),(0,[z7,z0,z2,z798,z4,z5]),(0,[z7,z0,z54,z3,z4,z36]),(0,[z7,z0,z2,z3,z376,z5])],[(0,[z170,z0,z420,z3,z4,z5]),(0,[z7,z0,z33,z3,z376,z5]),(0,[z7,z0,z22,z3,z4,z124]),(0,[z57,z7,z2,z58,z406,z5])],[(0,[z70,z1,z33,z3,z4,z5]),(0,[z15,z0,z931,z3,z4,z5])]],
   [[(0,[z186,z0,z22,z3,z4,z5]),(0,[z7,z0,z1145,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1146]),(0,[z7,z0,z2,z3,z4,z1147]),(0,[z7,z599,z2,z3,z4,z25]),(0,[z0,z33,z3,z4,z5,z379]),(0,[z7,z0,z2,z3,z954,z25])],[(0,[z492,z0,z566,z3,z4,z5]),(0,[z0,z1148,z2,z3,z4,z5])],[(0,[z0,z1,z84,z3,z4,z5]),(0,[z0,z228,z2,z3,z4,z93]),(0,[z1149,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z406,z5]),(0,[z7,z0,z1150,z3,z4,z5])],[(0,[z0,z249,z2,z3,z4,z5]),(0,[z228,z2,z73,z3,z4,z5]),(0,[z172,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z264,z5,z77]),(0,[z330,z2,z3,z4,z5,z25]),(0,[z7,z0,z1151,z3,z4,z5])],[(0,[z7,z0,z2,z1152,z4,z5]),(0,[z198,z1,z2,z3,z4,z25]),(0,[z7,z0,z1153,z3,z4,z5]),(0,[z7,z0,z358,z3,z4,z5]),(0,[z1154,z0,z2,z3,z4,z5])],[(0,[z1155,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z345]),(0,[z7,z0,z2,z572,z4,z25]),(0,[z7,z0,z2,z348,z4,z52]),(0,[z7,z0,z2,z3,z4,z1014])],[(0,[z7,z0,z106,z3,z4,z36]),(0,[z7,z0,z22,z3,z4,z200])],[(1,[z1,z2,z3,z4,z25]),(0,[z466,z1,z2,z3,z4,z25]),(0,[z7,z0,z2,z1156,z4,z5]),(0,[z47,z0,z2,z116,z4,z5]),(0,[z7,z0,z1157,z3,z4,z5]),(0,[z14,z7,z2,z3,z237,z166]),(0,[z7,z0,z966,z3,z4,z25])],[(0,[z7,z0,z1158,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z67])],[(0,[z7,z105,z2,z3,z4,z400]),(0,[z57,z1,z2,z58,z4,z5]),(0,[z7,z0,z2,z3,z4,z1159]),(0,[z7,z0,z1160,z3,z4,z5]),(0,[z7,z0,z1161,z3,z4,z5]),(0,[z7,z388,z0,z156,z4,z52]),(0,[z7,z0,z1162,z3,z4,z5])],[(0,[z0,z1,z122,z3,z4,z5]),(0,[z95,z0,z2,z3,z4,z159]),(0,[z7,z0,z439,z3,z4,z36]),(0,[z7,z0,z2,z156,z4,z314])],[(0,[z7,z1,z2,z3,z4,z25]),(0,[z7,z0,z1163,z3,z4,z5]),(0,[z7,z228,z22,z3,z4,z5]),(0,[z7,z0,z279,z3,z4,z5])],[(0,[z7,z0,z2,z3,z1164,z5])],[(0,[z1165,z7,z0,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1166]),(0,[z7,z0,z2,z3,z4,z1167]),(0,[z7,z0,z384,z3,z4,z5])]],
   [[(0,[z0,z1,z111,z3,z4,z5]),(0,[z7,z1168,z2,z3,z4,z5]),(0,[z7,z0,z1169,z3,z4,z5]),(0,[z0,z54,z82,z3,z4,z5]),(0,[z219,z0,z2,z3,z115,z25]),(0,[z7,z380,z0,z3,z4,z36]),(0,[z245,z0,z2,z3,z4,z25])],[(0,[z0,z1,z151,z3,z4,z5]),(0,[z1170,z0,z2,z3,z4,z5]),(0,[z7,z0,z1171,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z1172]),(0,[z0,z2,z3,z4,z5,z1173])],[(0,[z1,z2,z659,z3,z4,z5]),(0,[z7,z1174,z0,z3,z4,z5]),(0,[z7,z0,z1175,z3,z4,z5]),(0,[z1176,z0,z2,z3,z4,z5])],[(0,[z15,z0,z33,z3,z4,z5]),(0,[z7,z587,z2,z3,z4,z25]),(0,[z7,z0,z122,z3,z4,z159]),(0,[z7,z0,z1177,z3,z4,z5])],[(0,[z220,z0,z2,z3,z4,z5]),(0,[z13,z1,z2,z3,z4,z25]),(0,[z15,z0,z2,z3,z857,z4]),(0,[z293,z0,z2,z3,z4,z36]),(0,[z188,z7,z2,z3,z4,z25]),(0,[z1178,z0,z2,z3,z4,z5]),(0,[z1179,z0,z2,z3,z4,z5])],[(0,[z7,z229,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z175]),(0,[z15,z0,z22,z3,z4,z25]),(0,[z7,z228,z777,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z11]),(0,[z188,z7,z33,z3,z4,z25]),(0,[z0,z2,z3,z4,z5,z1180])],[(0,[z7,z33,z3,z660,z4,z5]),(0,[z7,z0,z2,z1181,z4,z5]),(0,[z944,z0,z2,z3,z4,z5])],[(0,[z7,z0,z350,z86,z4,z5])],[(0,[z1,z22,z3,z4,z5,z25]),(0,[z44,z0,z439,z3,z4,z5]),(0,[z0,z422,z168,z3,z4,z5]),(0,[z7,z388,z0,z3,z4,z25]),(0,[z7,z1182,z2,z3,z4,z5])],[(0,[z451,z1,z2,z3,z4,z5]),(0,[z61,z1,z22,z3,z4,z5])],[(0,[z15,z0,z2,z3,z4,z150]),(0,[z162,z0,z18,z3,z4,z25]),(0,[z7,z10,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z327,z75]),(0,[z0,z2,z3,z4,z5,z1183])],[(0,[z162,z0,z298,z3,z4,z5]),(0,[z76,z0,z3,z4,z5,z234])],[(0,[z7,z1184,z0,z3,z4,z5]),(0,[z7,z250,z33,z3,z4,z5]),(0,[z7,z0,z1185,z3,z4,z5]),(0,[z14,z281,z2,z3,z237,z5])],[(0,[z530,z15,z2,z3,z4,z5]),(0,[z7,z0,z1186,z3,z4,z36])],[(0,[z1,z2,z3,z682,z4,z5]),(0,[z7,z0,z269,z3,z4,z25]),(0,[z7,z0,z1187,z3,z4,z5]),(0,[z7,z0,z2,z652,z5,z77]),(0,[z7,z3,z4,z5,z234,z67])],[(0,[z7,z1188,z2,z3,z4,z5]),(0,[z7,z228,z2,z3,z4,z38]),(0,[z14,z7,z2,z3,z237,z5])]],
   [[(0,[z220,z0,z22,z3,z4,z5]),(0,[z7,z1189,z2,z3,z4,z5]),(0,[z7,z0,z1190,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1191]),(0,[z7,z2,z3,z4,z1192,z25]),(0,[z7,z0,z566,z3,z4,z25]),(0,[z1193,z0,z2,z3,z4,z36])],[(0,[z15,z1,z22,z3,z4,z5])],[(0,[z7,z0,z1194,z3,z4,z5])],[(0,[z0,z82,z2,z3,z4,z36]),(0,[z7,z0,z2,z4,z1195,z5])],[(0,[z7,z0,z29,z3,z4,z71]),(0,[z1196,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z1197,z5]),(0,[z7,z0,z2,z332,z4,z36]),(0,[z0,z2,z3,z4,z5,z1198]),(0,[z7,z0,z1199,z3,z4,z5])],[(0,[z1,z2,z454,z3,z4,z25]),(0,[z7,z0,z168,z3,z4,z35]),(0,[z0,z342,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z1054]),(0,[z0,z1200,z2,z3,z4,z5])],[(0,[z1201,z0,z2,z3,z4,z5]),(0,[z220,z0,z2,z3,z4,z35]),(0,[z7,z121,z0,z3,z4,z36]),(0,[z7,z0,z1202,z3,z4,z5])],[(0,[z7,z0,z431,z3,z4,z36])],[(0,[z15,z0,z65,z3,z4,z5]),(0,[z7,z102,z0,z3,z700,z5]),(0,[z117,z0,z33,z3,z4,z5]),(0,[z7,z550,z2,z3,z4,z25]),(0,[z7,z0,z3,z4,z25,z234])],[(0,[z7,z0,z3,z1203,z4,z5]),(0,[z7,z22,z3,z4,z5,z67]),(0,[z7,z0,z2,z3,z4,z1204]),(0,[z7,z0,z2,z3,z4,z1205])],[(0,[z0,z1,z33,z3,z4,z5]),(0,[z7,z0,z1206,z3,z4,z5]),(0,[z7,z0,z3,z1207,z4,z5]),(0,[z7,z421,z2,z3,z4,z25]),(0,[z1208,z0,z2,z3,z4,z5]),(0,[z7,z1209,z2,z3,z4,z5])],[(0,[z15,z0,z2,z3,z4,z313]),(0,[z7,z0,z33,z3,z4,z119]),(0,[z7,z0,z549,z3,z4,z520]),(0,[z530,z740,z2,z3,z4,z5])],[(0,[z7,z0,z29,z3,z4,z36]),(0,[z0,z1,z22,z3,z4,z25]),(0,[z15,z0,z2,z331,z3,z4]),(0,[z7,z228,z2,z68,z3,z4])],[(0,[z1210,z0,z2,z3,z4,z5]),(0,[z15,z543,z2,z3,z4,z5]),(0,[z17,z0,z248,z3,z4,z5]),(0,[z202,z0,z389,z3,z4,z93]),(0,[z1211,z0,z2,z3,z4,z5]),(0,[z7,z0,z3,z1212,z4,z5]),(0,[z60,z0,z221,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1213]),(0,[z0,z1,z866,z3,z4,z5]),(0,[z7,z0,z1214,z3,z4,z5]),(0,[z0,z2,z3,z792,z115,z5]),(0,[z7,z0,z1215,z3,z4,z5]),(0,[z7,z0,z1216,z3,z4,z5])]],
   [[(0,[z47,z0,z2,z48,z4,z25]),(0,[z7,z0,z49,z3,z4,z25]),(0,[z7,z0,z22,z3,z146,z6])],[(0,[z293,z0,z2,z3,z4,z125]),(0,[z7,z0,z2,z3,z4,z159])],[(0,[z0,z1,z2,z3,z4,z150]),(0,[z7,z1217,z0,z3,z4,z5]),(0,[z56,z7,z0,z3,z4,z127]),(0,[z0,z3,z4,z5,z481,z267])],[(0,[z7,z0,z1218,z3,z4,z36])],[(0,[z1006,z7,z0,z3,z4,z5]),(0,[z219,z0,z2,z3,z547,z115])],[(0,[z7,z229,z801,z3,z4,z5]),(0,[z7,z0,z3,z4,z901,z25]),(0,[z687,z7,z2,z3,z4,z25]),(0,[z56,z7,z0,z3,z4,z143]),(0,[z7,z0,z2,z3,z4,z124])],[(0,[z160,z1,z2,z3,z4,z25]),(0,[z64,z0,z1,z86,z4,z5]),(0,[z1219,z0,z2,z3,z4,z5]),(0,[z7,z0,z1220,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z177]),(0,[z1221,z0,z2,z3,z4,z5])],[(0,[z186,z0,z2,z3,z4,z5]),(0,[z1013,z61,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1222]),(0,[z416,z0,z2,z3,z376,z5]),(0,[z7,z0,z2,z572,z4,z520]),(0,[z7,z0,z1223,z3,z4,z5]),(0,[z0,z2,z3,z4,z36,z379])],[(0,[z70,z1,z2,z3,z4,z25]),(0,[z1,z2,z3,z4,z25,z52]),(0,[z7,z105,z106,z3,z4,z25]),(0,[z186,z0,z33,z3,z4,z5])],[(0,[z1,z1,z2,z3,z4,z25]),(0,[z7,z0,z3,z4,z5,z1224])],[(0,[z7,z0,z2,z3,z1225,z5]),(0,[z7,z0,z2,z3,z4,z1226])],[(0,[z1,z2,z68,z3,z4,z25]),(0,[z1227,z0,z2,z3,z4,z5]),(0,[z1228,z0,z2,z3,z4,z5])],[(0,[z7,z22,z33,z3,z4,z36]),(0,[z7,z0,z1229,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1230]),(0,[z7,z2,z3,z4,z25,z650]),(0,[z0,z1231,z2,z3,z4,z5]),(0,[z7,z0,z279,z3,z146,z4])],[(0,[z1,z2,z69,z3,z4,z25]),(0,[z172,z0,z2,z3,z4,z25]),(0,[z7,z0,z1232,z3,z4,z5]),(0,[z416,z0,z2,z3,z406,z5]),(0,[z7,z0,z1233,z3,z4,z5]),(0,[z0,z82,z3,z4,z5,z255]),(0,[z1234,z0,z2,z3,z4,z5]),(0,[z7,z0,z1235,z3,z4,z5])],[(0,[z7,z0,z1236,z3,z4,z5]),(0,[z7,z0,z384,z3,z146,z4])],[(0,[z15,z0,z2,z156,z4,z52]),(0,[z162,z0,z82,z3,z4,z5]),(0,[z7,z0,z1237,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z200]),(0,[z7,z0,z549,z3,z4,z25])]],
   [[(0,[z7,z0,z29,z3,z4,z400]),(0,[z1,z87,z2,z3,z4,z25]),(0,[z7,z0,z33,z3,z4,z200]),(0,[z0,z2,z3,z4,z5,z1238]),(0,[z7,z0,z221,z3,z4,z25])],[(0,[z0,z1,z65,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1239]),(0,[z7,z0,z621,z3,z120,z5])],[],[(0,[z70,z1,z375,z3,z4,z5])],[(0,[z7,z0,z1240,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z313]),(0,[z7,z228,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z972,z25]),(0,[z7,z0,z2,z3,z4,z1241]),(0,[z7,z0,z2,z3,z4,z1242]),(0,[z7,z0,z2,z110,z124,z77])],[(0,[z7,z0,z1243,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z71]),(0,[z0,z1,z2,z331,z3,z4]),(0,[z229,z1,z2,z3,z4,z5]),(0,[z17,z561,z0,z3,z4,z5]),(0,[z7,z228,z33,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z88]),(0,[z7,z0,z1244,z3,z4,z5])],[(0,[z7,z0,z549,z572,z4,z5]),(0,[z0,z2,z331,z3,z4,z379])],[(0,[z7,z0,z106,z3,z4,z5]),(0,[z219,z1,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z803,z4]),(0,[z15,z0,z2,z3,z547,z4]),(0,[z7,z0,z33,z3,z406,z5]),(0,[z57,z7,z2,z810,z4,z5])],[(0,[z172,z0,z2,z3,z4,z11]),(0,[z0,z249,z33,z3,z4,z5]),(0,[z530,z7,z2,z3,z85,z5]),(0,[z0,z1245,z2,z3,z4,z5]),(0,[z7,z0,z68,z279,z3,z4])],[(0,[z0,z1,z902,z3,z4,z5]),(0,[z15,z0,z2,z110,z5,z77]),(0,[z7,z0,z3,z4,z36,z263]),(0,[z281,z0,z439,z3,z4,z5]),(0,[z2,z3,z4,z5,z379,z67])],[(0,[z15,z0,z946,z3,z4,z5]),(0,[z330,z0,z215,z3,z4,z5]),(0,[z7,z160,z0,z3,z4,z34]),(0,[z7,z0,z2,z1246,z3,z4])],[(0,[z1,z2,z3,z58,z4,z25])],[(0,[z15,z0,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z1247])],[(1,[z1,z33,z3,z4,z25]),(0,[z15,z599,z2,z3,z4,z5]),(0,[z7,z0,z1248,z3,z4,z5]),(0,[z1249,z7,z0,z3,z4,z5])],[(0,[z7,z0,z375,z3,z4,z25]),(0,[z302,z0,z2,z3,z4,z200]),(0,[z0,z2,z3,z4,z36,z1250]),(0,[z7,z0,z1251,z3,z4,z36]),(0,[z296,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z1252,z4,z5])],[(0,[z7,z507,z33,z3,z4,z5]),(0,[z7,z102,z0,z3,z977,z5])]],
   [[(0,[z61,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z1068,z3,z25])],[(0,[z7,z1,z33,z3,z4,z25]),(0,[z7,z1253,z2,z3,z4,z5]),(0,[z7,z672,z0,z3,z120,z5]),(0,[z44,z0,z2,z3,z4,z36]),(0,[z7,z0,z880,z3,z4,z36])],[(0,[z50,z1,z2,z3,z4,z25]),(0,[z1,z2,z3,z4,z25,z25]),(0,[z162,z1,z2,z3,z4,z25]),(0,[z7,z1254,z2,z3,z4,z5]),(0,[z658,z0,z53,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1255]),(0,[z188,z330,z2,z3,z4,z25]),(0,[z56,z7,z0,z3,z4,z255])],[(0,[z15,z0,z2,z572,z4,z5]),(0,[z7,z64,z0,z753,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1256]),(0,[z7,z1257,z2,z3,z4,z5]),(0,[z7,z0,z2,z1258,z3,z4]),(0,[z7,z0,z995,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z1259])],[(0,[z0,z1,z923,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z213]),(0,[z7,z0,z2,z1260,z4,z5]),(0,[z7,z1261,z2,z3,z4,z5]),(0,[z7,z0,z215,z3,z4,z5]),(0,[z7,z0,z2,z110,z331,z77])],[(0,[z1,z132,z2,z3,z4,z25]),(0,[z7,z105,z2,z3,z4,z1192]),(0,[z7,z0,z168,z3,z4,z5]),(0,[z296,z0,z22,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z1262]),(0,[z1263,z0,z2,z3,z4,z5]),(0,[z76,z2,z3,z4,z5,z67]),(0,[z7,z0,z1264,z3,z4,z5])],[(0,[z15,z0,z375,z3,z4,z5]),(0,[z0,z1,z2,z156,z4,z52]),(0,[z202,z1,z2,z3,z4,z25]),(0,[z15,z0,z2,z3,z4,z11]),(0,[z7,z0,z2,z3,z4,z1265]),(0,[z7,z0,z65,z3,z376,z5])],[(0,[z7,z0,z3,z300,z4,z5]),(0,[z47,z0,z151,z3,z4,z5]),(0,[z7,z638,z2,z3,z4,z25]),(0,[z7,z0,z1266,z3,z4,z5]),(0,[z220,z0,z33,z3,z4,z5]),(0,[z56,z7,z0,z3,z4,z943])],[(0,[z15,z1,z2,z3,z4,z5]),(0,[z7,z0,z1267,z3,z4,z5]),(0,[z7,z229,z33,z3,z4,z5]),(0,[z7,z2,z639,z3,z4,z36])],[(0,[z7,z0,z2,z3,z4,z1268]),(0,[z530,z2,z3,z4,z5,z379])],[(0,[z228,z1,z2,z3,z4,z25]),(0,[z7,z0,z1269,z3,z4,z5]),(0,[z7,z254,z33,z3,z4,z5]),(0,[z1270,z0,z2,z3,z4,z5]),(0,[z1271,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z841,z4,z5]),(0,[z7,z0,z1272,z3,z4,z5]),(0,[z7,z0,z2,z3,z1197,z5]),(0,[z7,z0,z1186,z3,z4,z5]),(0,[z0,z422,z2,z3,z4,z508])],[(0,[z445,z1,z2,z3,z4,z5]),(0,[z7,z0,z1273,z3,z4,z5]),(0,[z7,z0,z65,z3,z406,z5])],[(0,[z7,z0,z2,z3,z4,z1274]),(0,[z7,z33,z3,z424,z4,z5])],[(0,[z1,z2,z73,z3,z4,z25]),(0,[z0,z1,z2,z3,z547,z4]),(0,[z293,z0,z22,z3,z4,z5]),(0,[z95,z0,z2,z3,z4,z36]),(0,[z1275,z7,z0,z3,z4,z36])]],
   [[(0,[z15,z0,z2,z980,z3,z4]),(0,[z7,z229,z2,z3,z4,z150]),(0,[z7,z0,z2,z1276,z4,z5]),(0,[z1193,z0,z2,z3,z4,z5]),(0,[z7,z0,z134,z3,z4,z5])],[(0,[z102,z0,z1,z3,z120,z5]),(0,[z0,z1,z2,z110,z5,z77]),(0,[z15,z638,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z1277,z5]),(0,[z7,z0,z1278,z3,z4,z5]),(0,[z0,z249,z2,z3,z4,z313])],[(0,[z63,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z945,z4,z5]),(0,[z898,z0,z2,z3,z4,z5]),(0,[z7,z380,z0,z32,z3,z4]),(0,[z7,z33,z3,z4,z36,z25]),(0,[z117,z0,z2,z3,z4,z25]),(0,[z281,z0,z2,z332,z4,z5]),(0,[z7,z0,z1279,z3,z4,z5]),(0,[z7,z0,z1280,z3,z4,z5])],[(0,[z7,z0,z3,z1281,z4,z5]),(0,[z0,z82,z2,z3,z4,z5]),(0,[z14,z7,z33,z3,z237,z5]),(0,[z7,z2,z659,z3,z4,z25]),(0,[z7,z0,z1282,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z25]),(0,[z15,z388,z0,z3,z4,z5]),(0,[z7,z0,z1283,z3,z4,z5]),(0,[z1284,z0,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z25,z67]),(0,[z7,z0,z2,z348,z4,z103]),(0,[z7,z2,z3,z660,z4,z36])],[(0,[z15,z0,z2,z3,z4,z285]),(0,[z7,z0,z2,z3,z1285,z5]),(0,[z7,z0,z2,z3,z4,z1286]),(0,[z7,z0,z1287,z3,z4,z5])],[(0,[z17,z0,z82,z3,z4,z5]),(0,[z0,z342,z221,z3,z4,z5])],[(0,[z452,z0,z157,z3,z4,z5]),(0,[z7,z0,z1288,z3,z4,z5]),(0,[z7,z0,z2,z3,z146,z6])],[(0,[z15,z0,z3,z4,z5,z481]),(0,[z7,z0,z33,z3,z146,z6]),(0,[z0,z1289,z2,z3,z4,z5])],[(0,[z7,z0,z1290,z3,z4,z5])],[(0,[z15,z0,z269,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1291]),(0,[z7,z326,z0,z435,z4,z5]),(0,[z530,z7,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z977,z5])],[(0,[z0,z1292,z2,z3,z4,z5]),(0,[z0,z1,z2,z572,z4,z5]),(0,[z416,z0,z2,z3,z4,z159])],[(0,[z7,z0,z1293,z3,z4,z5]),(0,[z1,z2,z3,z4,z25,z148]),(0,[z7,z0,z1294,z3,z4,z5]),(0,[z294,z7,z0,z3,z4,z217])],[(0,[z15,z0,z566,z3,z4,z5]),(0,[z7,z0,z939,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1295]),(0,[z7,z0,z131,z3,z4,z36]),(0,[z7,z0,z3,z4,z1296,z5])],[(0,[z7,z102,z0,z3,z120,z36]),(0,[z7,z1297,z0,z3,z4,z36]),(0,[z0,z1298,z2,z3,z4,z5])],[(0,[z57,z7,z2,z58,z4,z159]),(0,[z7,z0,z1299,z3,z4,z5]),(0,[z188,z7,z566,z3,z4,z25])]],
   [[(0,[z7,z0,z1300,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1301]),(0,[z7,z0,z22,z332,z4,z5]),(0,[z7,z0,z2,z3,z1302,z5])],[(0,[z7,z356,z33,z3,z4,z5]),(0,[z7,z1303,z0,z3,z4,z5]),(0,[z186,z0,z2,z3,z4,z25]),(0,[z1304,z0,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z25,z143]),(0,[z0,z1305,z2,z3,z4,z5])],[(0,[z702,z7,z2,z3,z4,z25]),(0,[z162,z0,z3,z4,z5,z464])],[(0,[z824,z0,z1,z3,z4,z5]),(0,[z7,z228,z2,z3,z146,z4]),(0,[z7,z0,z2,z1131,z4,z25]),(0,[z7,z0,z156,z279,z4,z52])],[(0,[z7,z0,z2,z3,z4,z1306]),(0,[z44,z0,z2,z332,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1307]),(0,[z0,z1308,z2,z3,z4,z5]),(0,[z1,z2,z320,z3,z4,z5]),(0,[z7,z0,z1309,z3,z4,z5]),(0,[z7,z1310,z2,z3,z4,z5]),(0,[z1311,z0,z2,z3,z4,z5]),(0,[z7,z0,z33,z3,z4,z159]),(0,[z7,z0,z2,z3,z1312,z5]),(0,[z1313,z0,z2,z3,z4,z5]),(0,[z7,z0,z712,z3,z4,z5]),(0,[z7,z0,z3,z94,z4,z175])],[(0,[z7,z0,z1137,z3,z4,z25])],[(0,[z381,z7,z0,z3,z4,z5]),(0,[z1314,z0,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1315]),(0,[z7,z501,z0,z3,z483,z5]),(0,[z7,z555,z22,z3,z4,z5]),(0,[z7,z0,z439,z3,z4,z166]),(0,[z0,z2,z3,z4,z5,z1316])],[(0,[z0,z1,z1085,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z67]),(0,[z17,z1,z2,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z1317]),(0,[z56,z7,z0,z3,z4,z363]),(0,[z7,z0,z33,z3,z4,z124]),(0,[z7,z1318,z0,z3,z4,z5])],[(0,[z7,z33,z3,z4,z5,z324]),(0,[z7,z0,z2,z3,z376,z25]),(0,[z7,z0,z2,z1319,z4,z5]),(0,[z1320,z0,z2,z3,z4,z5]),(0,[z7,z0,z1321,z3,z4,z5])],[(0,[z162,z0,z203,z3,z4,z5]),(0,[z47,z0,z283,z3,z4,z5]),(0,[z7,z0,z1322,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1323])],[(0,[z7,z0,z2,z3,z4,z71]),(0,[z15,z0,z2,z3,z4,z520]),(0,[z15,z0,z49,z3,z4,z5]),(0,[z7,z0,z389,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z88]),(0,[z1324,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z285]),(0,[z466,z0,z53,z3,z4,z5])],[(0,[z7,z0,z2,z1325,z4,z5]),(0,[z1,z2,z53,z3,z4,z25]),(0,[z7,z228,z2,z3,z4,z25]),(0,[z0,z2,z773,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1326]),(0,[z7,z0,z1327,z3,z4,z5])],[(0,[z56,z1,z2,z3,z4,z25]),(0,[z1,z2,z3,z4,z344,z5]),(0,[z7,z0,z54,z3,z4,z5]),(0,[z7,z229,z49,z3,z4,z5]),(0,[z7,z0,z727,z3,z4,z5]),(0,[z530,z76,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z481]),(0,[z1328,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z1329,z3,z4]),(0,[z60,z229,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z406,z25]),(0,[z7,z0,z1330,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z1331])],[(0,[z0,z249,z2,z3,z4,z25]),(0,[z76,z0,z2,z3,z4,z124])],[(0,[z0,z1,z269,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1332]),(0,[z281,z0,z2,z3,z4,z36]),(0,[z7,z0,z358,z3,z4,z25])],[(0,[z15,z0,z2,z3,z376,z5]),(0,[z7,z0,z2,z3,z818,z146])],[(0,[z7,z0,z1333,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z860]),(0,[z7,z0,z2,z753,z4,z5]),(0,[z7,z1334,z2,z3,z4,z5])],[(0,[z743,z1,z2,z3,z4,z5]),(0,[z0,z1,z566,z3,z4,z5]),(0,[z0,z33,z3,z4,z5,z267])],[(0,[z15,z0,z1038,z3,z4,z5]),(0,[z7,z0,z1335,z3,z4,z5]),(0,[z7,z2,z3,z4,z150,z25]),(0,[z7,z0,z1336,z3,z4,z5]),(0,[z7,z0,z1337,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1338]),(0,[z7,z2,z189,z572,z4,z5]),(0,[z7,z861,z3,z4,z5,z67])],[(0,[z1,z2,z3,z94,z4,z25]),(0,[z7,z0,z3,z4,z5,z901]),(0,[z0,z2,z3,z4,z5,z1339]),(0,[z7,z0,z1340,z3,z4,z5]),(0,[z7,z0,z3,z91,z4,z36]),(0,[z1341,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z4,z1195,z52])],[(0,[z7,z22,z397,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1342])],[(0,[z595,z1,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z406,z5]),(0,[z14,z7,z2,z3,z406,z5]),(0,[z0,z422,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z1343]),(0,[z0,z82,z16,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1344])],[(0,[z257,z0,z203,z3,z4,z5]),(0,[z281,z0,z22,z3,z4,z5]),(0,[z186,z0,z2,z3,z4,z285]),(0,[z7,z0,z279,z3,z4,z25]),(0,[z0,z82,z3,z4,z120,z5]),(0,[z0,z1345,z2,z3,z4,z5])],[(0,[z15,z0,z549,z3,z4,z5]),(0,[z7,z0,z65,z3,z4,z159]),(0,[z7,z0,z2,z3,z4,z1346])],[(0,[z15,z0,z221,z3,z4,z5]),(0,[z7,z0,z622,z3,z4,z36]),(0,[z7,z0,z1347,z3,z4,z5]),(0,[z7,z0,z384,z3,z4,z25])],[(0,[z7,z0,z269,z3,z4,z177]),(0,[z296,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1348])],[(0,[z551,z1,z2,z3,z4,z5]),(0,[z7,z0,z439,z3,z4,z5]),(0,[z7,z0,z2,z3,z1349,z5]),(0,[z7,z0,z2,z3,z4,z1350])],[(0,[z216,z1,z2,z3,z4,z25]),(0,[z7,z0,z1351,z3,z4,z5]),(0,[z7,z0,z2,z1352,z4,z5])]],
   [[(0,[z15,z0,z33,z3,z4,z25]),(0,[z7,z0,z1353,z3,z4,z5]),(0,[z309,z0,z2,z3,z4,z93]),(0,[z7,z0,z22,z3,z4,z36]),(0,[z7,z0,z490,z3,z4,z36])],[(0,[z632,z0,z18,z3,z4,z5]),(0,[z7,z0,z32,z3,z300,z4]),(0,[z0,z422,z22,z3,z4,z5]),(0,[z0,z1354,z22,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z1355]),(0,[z7,z0,z2,z332,z4,z166]),(0,[z220,z0,z2,z3,z4,z25])],[(0,[z1,z2,z3,z195,z4,z25]),(0,[z7,z0,z884,z3,z4,z5]),(0,[z7,z0,z106,z3,z4,z150]),(0,[z7,z380,z0,z3,z4,z5]),(0,[z7,z0,z284,z3,z4,z36]),(0,[z7,z229,z2,z3,z4,z25]),(0,[z7,z1356,z0,z3,z4,z5]),(0,[z7,z2,z1047,z3,z4,z67])],[(0,[z7,z0,z1357,z3,z4,z5]),(0,[z1358,z0,z2,z3,z4,z5]),(0,[z7,z0,z1359,z3,z4,z5]),(0,[z7,z0,z1171,z3,z4,z5]),(0,[z7,z0,z3,z4,z124,z234])],[(0,[z61,z1,z33,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z520]),(0,[z1,z2,z397,z3,z4,z5]),(0,[z0,z1,z49,z3,z4,z5]),(0,[z7,z0,z2,z3,z1360,z4]),(0,[z186,z0,z2,z3,z4,z313]),(0,[z7,z254,z2,z3,z4,z25]),(0,[z7,z0,z1361,z3,z4,z5])],[(0,[z1,z2,z3,z4,z25,z103]),(0,[z15,z0,z384,z3,z4,z5]),(0,[z7,z0,z2,z3,z1362,z5]),(0,[z7,z0,z1363,z3,z4,z5]),(0,[z7,z0,z1364,z3,z4,z5]),(0,[z7,z102,z0,z3,z402,z5])],[(0,[z293,z0,z2,z3,z4,z5])],[(0,[z14,z1,z33,z3,z4,z5]),(0,[z1,z2,z3,z4,z185,z25]),(0,[z56,z0,z1,z3,z4,z255]),(0,[z7,z0,z2,z1365,z3,z4]),(0,[z7,z10,z33,z3,z4,z25]),(0,[z7,z1366,z0,z3,z4,z5]),(0,[z64,z0,z82,z3,z4,z5])],[(0,[z188,z1,z2,z3,z4,z25]),(0,[z15,z0,z3,z4,z5,z234])],[(0,[z7,z0,z2,z3,z4,z1367]),(0,[z7,z0,z2,z3,z4,z1368]),(0,[z7,z0,z2,z3,z1369,z5]),(0,[z7,z0,z1370,z3,z4,z5]),(0,[z7,z0,z1371,z3,z4,z5])],[(0,[z573,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z1372,z3,z4]),(0,[z7,z0,z1373,z3,z4,z5]),(0,[z0,z249,z2,z3,z4,z285]),(0,[z7,z0,z1374,z3,z4,z5]),(0,[z1375,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z376,z5]),(0,[z7,z1376,z0,z3,z4,z5]),(0,[z7,z1377,z0,z3,z4,z5])],[(0,[z7,z0,z981,z3,z4,z5]),(0,[z1378,z0,z2,z3,z4,z5]),(0,[z44,z0,z22,z3,z4,z5]),(0,[z14,z7,z2,z3,z237,z25]),(0,[z1379,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1195])],[(0,[z15,z1,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1380]),(0,[z7,z0,z2,z3,z4,z1381])],[(0,[z583,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z1382,z4,z5]),(0,[z1275,z7,z0,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1383])],[(0,[z1384,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z32,z3,z4]),(0,[z7,z0,z1385,z3,z4,z5]),(0,[z7,z22,z396,z3,z4,z5]),(0,[z0,z87,z82,z3,z4,z5])]],
   [[(0,[z7,z0,z3,z4,z5,z263]),(0,[z7,z0,z1386,z3,z4,z5]),(0,[z57,z7,z2,z572,z4,z5]),(0,[z7,z0,z84,z3,z4,z36]),(0,[z7,z0,z1387,z3,z4,z5])],[(0,[z7,z0,z2,z3,z1388,z4]),(0,[z7,z396,z2,z3,z4,z25]),(0,[z7,z2,z3,z4,z5,z1389]),(0,[z0,z1390,z2,z3,z4,z5]),(0,[z7,z0,z1391,z3,z4,z5])],[(0,[z219,z0,z3,z300,z115,z5]),(0,[z7,z0,z2,z3,z1392,z5]),(0,[z0,z2,z3,z4,z5,z1393]),(0,[z7,z0,z2,z3,z4,z1394])],[(0,[z7,z0,z22,z3,z4,z400]),(0,[z0,z1,z549,z3,z4,z5]),(0,[z1,z2,z156,z3,z4,z25]),(0,[z7,z0,z1395,z3,z4,z5]),(0,[z14,z7,z2,z572,z237,z5])],[(0,[z0,z1,z221,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z1396]),(0,[z7,z0,z3,z753,z4,z5])],[(0,[z1397,z0,z2,z3,z4,z5]),(0,[z596,z1,z2,z3,z4,z5]),(0,[z0,z53,z321,z3,z4,z5]),(0,[z7,z0,z1398,z3,z4,z5]),(0,[z7,z0,z2,z1399,z3,z4]),(0,[z7,z50,z33,z3,z4,z25]),(0,[z7,z2,z3,z810,z4,z5]),(0,[z7,z0,z2,z156,z4,z521])],[(0,[z7,z1400,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z508]),(0,[z7,z0,z2,z3,z4,z1401])],[(0,[z0,z82,z33,z3,z4,z5]),(0,[z7,z0,z2,z332,z4,z5]),(0,[z0,z1402,z2,z3,z4,z5]),(0,[z1403,z0,z2,z3,z4,z5])],[(0,[z0,z1,z33,z3,z4,z25]),(0,[z1,z448,z2,z3,z4,z25]),(0,[z1,z2,z3,z48,z4,z25]),(0,[z7,z0,z2,z3,z4,z1404])],[(0,[z7,z0,z3,z1405,z4,z5]),(0,[z7,z0,z2,z3,z4,z1406]),(0,[z7,z0,z122,z3,z4,z36]),(0,[z530,z7,z2,z3,z4,z5]),(0,[z7,z121,z0,z3,z4,z5])],[(0,[z7,z356,z2,z3,z4,z25]),(0,[z1407,z0,z2,z3,z4,z5]),(0,[z95,z0,z22,z3,z4,z5]),(0,[z7,z0,z431,z3,z4,z5]),(0,[z7,z1408,z2,z3,z4,z5])],[(0,[z193,z1,z2,z3,z4,z25]),(0,[z7,z0,z2,z849,z4,z5]),(0,[z7,z0,z3,z4,z5,z1409]),(0,[z197,z228,z2,z3,z4,z5]),(0,[z281,z0,z2,z3,z4,z166]),(0,[z7,z2,z3,z4,z5,z1410]),(0,[z7,z0,z1411,z3,z4,z5])],[(0,[z219,z0,z2,z3,z418,z5]),(0,[z7,z64,z0,z86,z4,z36]),(0,[z7,z3,z4,z5,z949,z67])],[(0,[z7,z0,z2,z3,z4,z1412]),(0,[z7,z0,z22,z3,z4,z125]),(0,[z7,z0,z2,z3,z4,z1413]),(0,[z7,z1297,z0,z3,z4,z5]),(0,[z7,z0,z1414,z3,z4,z5])],[(0,[z17,z0,z53,z3,z4,z36]),(0,[z7,z0,z151,z3,z4,z36]),(0,[z7,z228,z49,z3,z4,z5]),(0,[z7,z1415,z0,z3,z4,z5]),(0,[z7,z0,z39,z3,z4,z36]),(0,[z7,z0,z2,z1416,z4,z5]),(0,[z7,z2,z3,z4,z716,z5]),(0,[z7,z0,z155,z3,z4,z36]),(0,[z7,z0,z2,z3,z818,z6])],[(0,[z7,z0,z29,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1417]),(0,[z7,z0,z53,z3,z4,z175]),(0,[z0,z18,z773,z3,z4,z5]),(0,[z1418,z0,z2,z3,z4,z5]),(0,[z1419,z0,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z234]),(0,[z7,z0,z973,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1420]),(0,[z1421,z0,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z36,z324])],[(0,[z15,z0,z3,z4,z5,z1108]),(0,[z15,z0,z2,z3,z4,z119]),(0,[z7,z0,z132,z321,z4,z5]),(0,[z381,z7,z0,z3,z4,z25]),(0,[z7,z0,z165,z3,z4,z36])],[(0,[z0,z1,z375,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z11])],[(0,[z492,z0,z215,z3,z4,z5])],[(0,[z0,z1,z2,z1068,z3,z5]),(0,[z7,z0,z1422,z3,z4,z5]),(0,[z7,z0,z1423,z3,z4,z5]),(0,[z7,z0,z1223,z3,z4,z25]),(0,[z1424,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1071,z3,z4]),(0,[z7,z0,z3,z979,z4,z5]),(0,[z530,z7,z22,z3,z4,z5]),(0,[z7,z0,z1218,z3,z4,z5]),(0,[z1425,z0,z2,z3,z4,z5])],[(0,[z7,z0,z1426,z3,z4,z5]),(0,[z7,z0,z820,z3,z4,z5])],[(0,[z197,z1,z2,z3,z4,z25]),(0,[z56,z7,z0,z3,z4,z436]),(0,[z7,z0,z1427,z3,z4,z5])],[(0,[z57,z15,z2,z58,z4,z5]),(0,[z7,z0,z3,z1428,z4,z5])],[(0,[z7,z0,z3,z1429,z4,z5]),(0,[z7,z0,z3,z4,z5,z1430])],[(0,[z1,z2,z3,z4,z25,z255])],[(0,[z0,z1,z1080,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z177]),(0,[z0,z2,z3,z4,z36,z267])],[(0,[z381,z0,z1,z3,z4,z5]),(0,[z330,z0,z2,z3,z4,z36])],[(0,[z7,z0,z3,z1431,z4,z5]),(0,[z44,z0,z2,z3,z4,z166]),(0,[z1432,z0,z2,z3,z4,z5])],[(0,[z7,z0,z993,z3,z4,z5]),(0,[z7,z22,z33,z3,z4,z5])],[(0,[z135,z0,z18,z3,z4,z5])]],
   [[(0,[z7,z0,z33,z3,z4,z71]),(0,[z0,z1,z1096,z3,z4,z5]),(0,[z7,z105,z22,z3,z4,z25]),(0,[z7,z0,z33,z3,z4,z88]),(0,[z7,z0,z2,z3,z4,z1433])],[(0,[z281,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1434]),(0,[z7,z353,z33,z3,z4,z5]),(0,[z7,z0,z1435,z3,z4,z5]),(0,[z1436,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1437])],[(0,[z7,z2,z3,z4,z5,z1438]),(0,[z7,z0,z1439,z3,z4,z5]),(0,[z1440,z0,z2,z3,z4,z5])],[(0,[z95,z0,z122,z3,z4,z5]),(0,[z7,z0,z2,z189,z406,z5]),(0,[z0,z1441,z2,z3,z4,z5]),(0,[z7,z0,z1442,z3,z4,z5])],[(0,[z1,z157,z2,z3,z4,z25]),(0,[z7,z0,z106,z3,z4,z25]),(0,[z162,z0,z54,z3,z4,z5]),(0,[z202,z0,z22,z3,z4,z93]),(0,[z7,z0,z1443,z3,z4,z5]),(0,[z7,z121,z0,z331,z3,z4]),(0,[z1444,z0,z2,z3,z4,z5])],[(0,[z0,z1445,z2,z3,z4,z5]),(0,[z15,z0,z2,z3,z4,z200])],[(0,[z7,z0,z970,z3,z4,z5]),(0,[z7,z0,z3,z91,z4,z5]),(0,[z7,z1446,z0,z3,z4,z5]),(0,[z7,z0,z1447,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z36]),(0,[z130,z1,z2,z3,z4,z25]),(0,[z7,z0,z1448,z3,z4,z5]),(0,[z7,z1449,z2,z3,z4,z5]),(0,[z1450,z7,z0,z3,z4,z5]),(0,[z117,z0,z2,z3,z4,z119]),(0,[z1451,z0,z2,z3,z4,z5])],[(0,[z1,z2,z3,z85,z4,z25]),(0,[z0,z422,z2,z3,z4,z5]),(0,[z0,z1354,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1452]),(0,[z1453,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z119]),(0,[z7,z1454,z2,z3,z4,z5])],[(0,[z61,z1,z221,z3,z4,z5]),(0,[z15,z228,z2,z3,z4,z5])],[(0,[z7,z0,z622,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1455]),(0,[z7,z463,z33,z3,z4,z5]),(0,[z337,z7,z2,z3,z4,z25])],[(0,[z7,z0,z2,z3,z851,z5]),(0,[z202,z0,z3,z4,z263,z93]),(0,[z14,z7,z2,z3,z237,z520]),(0,[z7,z0,z1456,z3,z4,z5])],[(0,[z61,z1,z2,z3,z4,z25])],[(0,[z15,z0,z358,z3,z4,z5]),(0,[z202,z0,z2,z3,z4,z860]),(0,[z7,z2,z3,z4,z124,z67])],[(0,[z7,z0,z22,z3,z4,z5]),(0,[z7,z0,z2,z3,z1457,z5]),(0,[z250,z1,z2,z3,z4,z5]),(1,[z0,z773,z3,z4,z5]),(0,[z7,z0,z490,z3,z4,z5]),(0,[z7,z0,z3,z4,z977,z5])]],
   [[(0,[z14,z1,z2,z3,z4,z25]),(0,[z7,z0,z1251,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1458]),(0,[z1,z534,z2,z3,z4,z5]),(0,[z7,z0,z284,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z379]),(0,[z7,z0,z283,z3,z4,z36]),(0,[z296,z0,z33,z3,z4,z5]),(0,[z1459,z0,z2,z3,z4,z5])],[(0,[z7,z0,z1460,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1461]),(0,[z7,z0,z215,z3,z4,z25])],[(0,[z0,z1,z2,z3,z4,z177]),(0,[z44,z0,z2,z3,z4,z5]),(0,[z15,z2,z3,z4,z5,z67]),(0,[z7,z0,z880,z3,z4,z5]),(0,[z7,z0,z773,z3,z4,z5]),(0,[z7,z261,z2,z3,z4,z25]),(0,[z7,z0,z168,z3,z4,z25])],[(0,[z172,z10,z33,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z1452]),(0,[z7,z333,z2,z3,z4,z25]),(0,[z7,z0,z875,z3,z4,z36])],[(0,[z0,z1462,z2,z3,z4,z5]),(0,[z7,z0,z3,z300,z4,z25])],[(0,[z15,z1,z2,z3,z4,z25]),(0,[z15,z0,z279,z3,z4,z5]),(0,[z7,z0,z995,z3,z4,z5]),(0,[z7,z1463,z2,z3,z4,z5]),(0,[z7,z0,z1464,z3,z4,z5]),(0,[z7,z0,z2,z32,z3,z4]),(0,[z302,z0,z2,z3,z4,z36]),(0,[z7,z0,z2,z3,z4,z1465]),(0,[z1466,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1131,z4,z5]),(0,[z7,z0,z2,z1033,z4,z5]),(0,[z7,z0,z1467,z3,z4,z5]),(0,[z7,z0,z431,z156,z4,z52])],[(0,[z1,z2,z3,z238,z4,z25]),(0,[z7,z0,z2,z3,z4,z1468])],[(0,[z7,z2,z3,z4,z662,z25]),(0,[z7,z2,z3,z85,z406,z5]),(0,[z7,z0,z1469,z3,z4,z5]),(0,[z1470,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z1197,z25]),(0,[z7,z0,z2,z3,z4,z1471]),(0,[z0,z1472,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z400]),(0,[z7,z0,z3,z1473,z4,z5]),(0,[z0,z54,z53,z3,z4,z5]),(0,[z7,z0,z1474,z3,z4,z5]),(0,[z293,z0,z33,z3,z4,z5]),(0,[z7,z0,z2,z1475,z3,z4])],[(0,[z7,z0,z33,z3,z4,z400]),(0,[z0,z1,z2,z1138,z4,z5]),(0,[z1,z555,z2,z3,z4,z5]),(0,[z15,z0,z215,z3,z4,z5]),(0,[z1476,z0,z2,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z785]),(0,[z14,z7,z549,z3,z237,z5]),(0,[z0,z422,z2,z3,z4,z35])],[(0,[z219,z380,z0,z3,z115,z5]),(0,[z7,z705,z33,z3,z4,z5]),(0,[z7,z0,z1477,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z200]),(0,[z57,z7,z33,z3,z4,z25]),(0,[z7,z0,z2,z3,z4,z508]),(0,[z7,z0,z134,z3,z4,z25]),(0,[z7,z0,z2,z1478,z4,z5]),(0,[z0,z1479,z2,z3,z4,z5]),(0,[z530,z7,z2,z3,z4,z829])],[(0,[z162,z0,z157,z3,z4,z5]),(0,[z138,z0,z53,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z1480]),(0,[z7,z0,z3,z4,z5,z1481]),(0,[z7,z1482,z2,z3,z4,z5]),(0,[z1483,z0,z2,z3,z4,z5])],[(0,[z63,z1,z2,z3,z4,z25]),(0,[z7,z0,z1484,z3,z4,z5]),(0,[z7,z0,z3,z493,z4,z255])]],
   [[(0,[z7,z0,z1485,z3,z4,z5]),(0,[z188,z492,z2,z3,z4,z25]),(0,[z0,z82,z2,z3,z4,z25]),(0,[z0,z2,z3,z4,z25,z1338]),(0,[z7,z0,z1282,z3,z4,z25]),(0,[z7,z121,z0,z110,z5,z77])],[(0,[z95,z0,z2,z3,z4,z5]),(0,[z1486,z0,z2,z3,z4,z5]),(0,[z0,z1487,z2,z3,z4,z5])],[(0,[z7,z0,z2,z3,z4,z1192]),(0,[z1,z2,z276,z3,z4,z25]),(0,[z1488,z0,z2,z3,z4,z5]),(0,[z7,z0,z22,z3,z4,z35]),(0,[z7,z0,z1489,z3,z4,z5])],[(0,[z7,z0,z3,z1048,z4,z5]),(0,[z15,z10,z33,z3,z4,z5]),(0,[z7,z0,z2,z3,z1490,z5]),(0,[z7,z0,z22,z1033,z4,z5])],[(0,[z0,z1,z2,z3,z406,z5]),(0,[z7,z0,z1491,z3,z4,z5]),(0,[z7,z0,z1492,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z125]),(0,[z7,z0,z1288,z3,z4,z25]),(0,[z0,z2,z3,z4,z5,z1493])],[(0,[z7,z10,z33,z3,z4,z11]),(0,[z7,z0,z2,z3,z376,z159]),(0,[z7,z0,z2,z849,z4,z25]),(0,[z7,z0,z2,z3,z4,z1494]),(0,[z0,z3,z4,z5,z234,z379]),(0,[z7,z0,z1495,z3,z4,z5])],[(0,[z14,z1,z2,z3,z237,z5]),(0,[z0,z1,z358,z3,z4,z5]),(0,[z7,z0,z2,z110,z36,z77]),(0,[z7,z0,z3,z4,z5,z943])],[(0,[z45,z1,z2,z3,z4,z5])],[(0,[z202,z0,z2,z3,z4,z662]),(0,[z809,z0,z2,z3,z4,z5]),(0,[z170,z0,z248,z3,z4,z5]),(0,[z7,z0,z2,z58,z406,z5]),(0,[z0,z2,z3,z4,z5,z1250]),(0,[z1496,z0,z2,z3,z4,z5])],[(0,[z15,z0,z3,z1281,z4,z5]),(0,[z7,z534,z33,z3,z4,z5])],[(0,[z1,z22,z33,z3,z4,z5]),(0,[z7,z569,z2,z3,z4,z25]),(0,[z1497,z0,z2,z3,z4,z5])],[(0,[z7,z0,z33,z332,z4,z5]),(0,[z7,z0,z2,z3,z406,z159]),(0,[z7,z64,z0,z86,z4,z5])],[(0,[z162,z0,z3,z697,z4,z5]),(0,[z530,z7,z121,z3,z4,z5]),(0,[z7,z0,z2,z156,z4,z1195])],[(0,[z64,z1,z2,z3,z4,z25]),(0,[z15,z0,z2,z3,z146,z6]),(0,[z7,z0,z3,z1028,z4,z5]),(0,[z7,z0,z2,z3,z4,z1498]),(0,[z7,z0,z2,z3,z4,z1499]),(0,[z7,z0,z1500,z3,z4,z5]),(0,[z7,z0,z39,z3,z4,z5]),(0,[z530,z7,z33,z3,z4,z5]),(0,[z7,z0,z1501,z3,z4,z5])],[(0,[z1,z2,z189,z3,z4,z25]),(0,[z0,z1,z279,z3,z4,z5]),(0,[z7,z2,z567,z3,z4,z25]),(0,[z7,z0,z3,z4,z5,z1502])],[(0,[z145,z0,z2,z8,z4,z5]),(0,[z7,z0,z2,z3,z4,z1503]),(0,[z7,z0,z131,z3,z4,z5]),(0,[z7,z0,z2,z3,z4,z819]),(0,[z7,z0,z22,z3,z4,z345]),(0,[z7,z2,z3,z424,z4,z36]),(0,[z7,z0,z1504,z3,z4,z5]),(0,[z0,z1505,z2,z3,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1380).take 215) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1595)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 460, 215] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 116).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 229).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 345).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 450).take 62).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [116, 113, 116, 105, 62] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_36757

theorem PEqualNP.Outside.L_meta_36757 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373472 * 2 ^ 32 + 4008241376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36757.solve