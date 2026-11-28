import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42868

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
  Nat.testBit (4276676840 * 2 ^ 32 + 4001949832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00c3450d10d43560#64 ++ 0x00030d14344350d5#64 ++ 0x01c7cf1f31fc7fdf#64 ++ 0xe4071f3c7cc7f1ff#64 : BitVec 256),
   (0x0618926246298a80#64 ++ 0x201862498918a62a#64 ++ 0x0e38f3e3ce3f8ff7#64 ++ 0xec38e3cf8f38fe3f#64 : BitVec 256),
   (0x702d28b4f032d301#64 ++ 0x15c0b4a2d3c0cb4c#64 ++ 0xf03f3cfcf033f33b#64 ++ 0xb7c0fcf3f3c0cfcc#64 : BitVec 256),
   (0xbb403f00ab436c00#64 ++ 0x4aed00fc02ad0db0#64 ++ 0xffc03f00ffc3fc3f#64 ++ 0x7bff00fc03ff0ff0#64 : BitVec 256),
   (0xddbfc000fdbc0004#64 ++ 0x9376ff0003f6f000#64 ++ 0xffffc000fffc003d#64 ++ 0xdbffff0003fff000#64 : BitVec 256),
   (0xeff6ffdb00000002#64 ++ 0x8fbfdbff6c000000#64 ++ 0xffffffff0000003e#64 ++ 0x9ffffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [7, 2]⟩, ⟨.and, [7, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00c2450900c42460 0x0003091424031091 0x01c0c30301cc0cc4 0x4007030c0c073033

def z1 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cf1f31fc7fdf 0xe4071f3c7cc7f1ff

def z2 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f3e3ce3f8ff7 0xec38e3cf8f38fe3f

def z3 : W := mkw 0x70ef6dbdf0f6f761 0x15c3bdb6f7c3dbdd 0xf1fffffff1ffffff 0xf7c7ffffffc7ffff

def z4 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03f00ffc3fc3f 0x7bff00fc03ff0ff0

def z5 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc000fffc003d 0xdbffff0003fff000

def z6 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff0000003e 0x9ffffffffc000000

def z7 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf033f33b 0xb7c0fcf3f3c0cfcc

def z8 : W := mkw 0xd9e7450db9d43564 0x93679d1436e750d5 0xf1c7cf1f31fc7fdf 0xf7c71f3c7cc7f1ff

def z9 : W := mkw 0x10000000ab436c00 0x4040000002ad0db0 0x00000000ffc3fc01 0x6000000003ff0ff0

def z10 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc00000ffc0003d 0x5bff000003ff0000

def z11 : W := mkw 0x0040050900000000 0x0001001424000000 0x00000f1f00000002 0x0400003c7c000000

def z12 : W := mkw 0x8d92c0000d8c0004 0x82364b0000363000 0x0fc0c0000fcc0004 0x483f0300003f3000

def z13 : W := mkw 0xdd3c8000ed280004 0x9374f20003b4a000 0xfe380000ce000020 0x1bf8e00003380000

def z14 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x01c03f0031c3fc1f 0x600700fc00c70ff0

def z15 : W := mkw 0xeffefffb40208202 0x8fbffbffed008208 0xffffffffc033833f 0xbfffffffff00ce0c

def z16 : W := mkw 0x0200120002010800 0x0008004800080420 0x0e003300ce038c37 0x683800cc03380e30

def z17 : W := mkw 0xbf58bf62ef6bee80 0x6afd62fd8bbdafba 0xfff8ffe3ffffffff 0xffffe3ff8fffffff

def z18 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03f3cfc0000003a 0x97c0fcf3f0000000

def z19 : W := mkw 0x0610924200000000 0x0018424908000000 0x0e38f3e300000036 0x8c38e3cf8c000000

def z20 : W := mkw 0xeb643f9000000000 0x0fad90fe40000000 0xffff3ffc0000003e 0x9ffffcfff0000000

def z21 : W := mkw 0xfb6d3fb4fb73ff01 0x5fedb4fed3edcffc 0xffff3ffcfff3ff3f 0xfffffcfff3ffcffc

def z22 : W := mkw 0x0009002450309301 0x100024009140c24c 0x0000000000300300 0x000000000000c00c

def z23 : W := mkw 0x4024000000000000 0x0100900000000000 0xf03f000000000038 0x93c0fc0000000000

def z24 : W := mkw 0x8900000000000000 0x0224000000000000 0xffc000000000003c 0x1bff000000000000

def z25 : W := mkw 0x74bfe8b4f4bed305 0x95d2ffa2d3d2fb4c 0xf03ffcfcf03ff33b 0xb7c0fff3f3c0ffcc

def z26 : W := mkw 0xb9002800a9024000 0x4ae400a002a40900 0xf000000000000000 0x13c0000000000000

def z27 : W := mkw 0xdfbfd242fdbc0004 0x937eff490bf6f000 0xfffff3e3fffc003f 0xdfffffcf8ffff000

def z28 : W := mkw 0x70242890a0024001 0x15c090a242800900 0xf000000000000000 0x13c0000000000000

def z29 : W := mkw 0xdfffd76ffffdbfe4 0xb37fff5dbffff6ff 0xffffffffffffffff 0xffffffffffffffff

def z30 : W := mkw 0x0083400d10941160 0x00020d0034425045 0x0007001c00000000 0x00001c0070000000

def z31 : W := mkw 0xddbfc00dfdbc1164 0x9376ff0037f6f045 0xffffc01ffffc03fd 0xdfffff007ffff00f

def z32 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x00003f000003fc02 0x200000fc00000ff0

def z33 : W := mkw 0x8b4017000b412c00 0x4a2d005c002d04b0 0x0fc003000fc00c04 0x483f000c003f0030

def z34 : W := mkw 0xeff6ffdb0d8c0006 0x8fbfdbff6c363000 0xffffffff0fcc003e 0xdffffffffc3f3000

def z35 : W := mkw 0x22403fdb00000002 0x0c8900ff6c000000 0x00003fff00000002 0x040000fffc000000

def z36 : W := mkw 0xffffffdbfdbc0006 0x9fffffff6ff6f000 0xfffffffffffc003f 0xdffffffffffff000

def z37 : W := mkw 0xcdb6c0db00000002 0x8736db036c000000 0xffffc0ff0000003c 0x9fffff03fc000000

def z38 : W := mkw 0x300928b4f032d301 0x14c024a2d3c0cb4c 0x00003cfcf033f303 0x240000f3f3c0cfcc

def z39 : W := mkw 0xcdb6c00000000000 0x8336db0000000000 0xffffc0000000003c 0x9bffff0000000000

def z40 : W := mkw 0xdd3c8000ed280004 0x9374f20003b4a000 0xfe38c000ce3c0035 0xdbf8e3000338f000

def z41 : W := mkw 0x0040050000402400 0x0001001400010090 0x01c00f0031c07c1f 0x6007003c00c701f0

def z42 : W := mkw 0x0008002040208200 0x0000200081008208 0x003830e0c0338333 0xa400e0c38300ce0c

def z43 : W := mkw 0x763dbaf6f63bdb81 0x35d8f6ebdbd8ef6e 0xfe3ffffffe3fffff 0xfff8fffffff8ffff

def z44 : W := mkw 0x0008002046298a80 0x200020008118a62a 0x00000000ce3f8fc1 0x600000000338fe3f

def z45 : W := mkw 0xef74bfd200000002 0x8fbdd2ff48000000 0xfff83fe00000003e 0x1bffe0ff80000000

def z46 : W := mkw 0x0240170002412c00 0x4809005c000904b0 0x0000030000000c00 0x0000000c00000030

def z47 : W := mkw 0xf92d28b4f932d301 0x17e4b4a2d3e4cb4c 0xffff3cfcfff3f33f 0xfffffcf3f3ffcfcc

def z48 : W := mkw 0xffffff00ffff6c04 0xdbfffffc03fffdb0 0xffffff00fffffc3f 0xfbfffffc03fffff0

def z49 : W := mkw 0x0200126202018a80 0x200800498808062a 0x0e0033e3ce038ff7 0x6c3800cf8f380e3f

def z50 : W := mkw 0x00c2450900000000 0x0003091424000000 0x01c7cf1f0000001e 0x84071f3c7c000000

def z51 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00000000f033f301 0x2000000003c0cfcc

def z52 : W := mkw 0x16199266f63bdb81 0x305866499bd8ef6e 0x0e38f3e3fe3ffff7 0xec38e3cf8ff8ffff

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000300313 0xa40000000000c00c

def z54 : W := mkw 0x70252894b0125101 0x15c094a252c04944 0xf0070c1c30007008 0x13c01c3070c001c0

def z55 : W := mkw 0x0200126202018a80 0x200800498808062a 0x000033e300038fc2 0x240000cf8c000e3f

def z56 : W := mkw 0x0418800044280000 0x001062000110a000 0x0e38c000ce3c0035 0xc838e3000338f000

def z57 : W := mkw 0x10090000f0300000 0x1040240003c0c000 0x00000000f0300001 0x0000000003c0c000

def z58 : W := mkw 0x0000000002436c00 0x4000000000090db0 0x000000000003fc00 0x2000000000000ff0

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c30300000016 0x8400030c0c000000

def z60 : W := mkw 0xbb003a00ab034800 0x4aec00e802ac0d20 0xfe003000ce038020 0x1bf800c003380e00

def z61 : W := mkw 0xe9e76d9d10d43562 0x8fa79db6744350d5 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z62 : W := mkw 0xfffffffff63bdb83 0xbfffffffffd8ef6e 0xfffffffffe3fffff 0xfffffffffff8ffff

def z63 : W := mkw 0x10090024fdbed305 0x1040240093f6fb4c 0x00000000fffff301 0x6000000003ffffcc

def z64 : W := mkw 0xfdbfe8b4fdbed305 0x97f6ffa2d3f6fb4c 0xfffffcfcfffff33f 0xfffffff3f3ffffcc

def z65 : W := mkw 0xcdb6c0000d8c0004 0x8336db0000363000 0xffffc0000fcc003c 0xdbffff00003f3000

def z66 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xfe000000ce000020 0x1bf8000003380000

def z67 : W := mkw 0x10090000fdbc0004 0x1040240003f6f000 0x00000000fffc0001 0x4000000003fff000

def z68 : W := mkw 0x44bfc00054bc0004 0x9112ff000152f000 0x003fc000003c0000 0x8000ff000000f000

def z69 : W := mkw 0x8d9ac0004dac0004 0x82366b000136b000 0x0ff8c000cffc0035 0xc83fe300033ff000

def z70 : W := mkw 0xddbec000edac0004 0x9376fb0003b6b000 0xfff8c000cfcc0024 0x5bffe300033f3000

def z71 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f0e3ce3f83e0 0x8c38e3c38f38fe0f

def z72 : W := mkw 0x0418806244288280 0x201062018910a20a 0x0038c0e3003c03c0 0x8400e3038c00f00f

def z73 : W := mkw 0x22403fb40243ff01 0x4c8900fed0090ffc 0x00003ffc0003ff02 0x240000fff0000ffc

def z74 : W := mkw 0x44bfc0b454bc9305 0x9512ff02d152f24c 0x003fc0fc003c0300 0x8400ff03f000f00c

def z75 : W := mkw 0x44b6c0db00000002 0x8512db036c000000 0x003fc0ff00000000 0x8400ff03fc000000

def z76 : W := mkw 0x8b0012000b010800 0x4a2c0048002c0420 0x0e0000000e000000 0x0838000000380000

def z77 : W := mkw 0xef34bad200000002 0x8fbcd2eb48000000 0xfe3830e000000020 0x1bf8e0c380000000

def z78 : W := mkw 0xfff6ffdbab436c02 0xcfffdbff6ead0db0 0xffffffffffc3fc3f 0xffffffffffff0ff0

def z79 : W := mkw 0x602428b40002d301 0x058090a2d0000b4c 0xf03f3cfc0003f33a 0xb7c0fcf3f0000fcc

def z80 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc303fffc0fff 0xffffff0c0ffff03f

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c303003c0fd7 0xe400030c0c00f03f

def z82 : W := mkw 0x06dbd76f56fdbfe0 0x201b6f5dbd5bf6ff 0x0fffffffffffffff 0xec3fffffffffffff

def z83 : W := mkw 0xfff6ffdbab034802 0xcfffdbff6eac0d20 0xffffffffce03803e 0x9fffffffff380e00

def z84 : W := mkw 0x10090024fb73ff01 0x5040240093edcffc 0x00000000fff3ff01 0x6000000003ffcffc

def z85 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c0c30331fc7fc5 0x6007030c0cc7f1ff

def z86 : W := mkw 0xab403f0000000000 0x0aad00fc00000000 0xffc03f000000003e 0x1bff00fc00000000

def z87 : W := mkw 0x3618ba62e62bca80 0x20d862e98b98af2a 0xfe38ffe3fe3fffff 0xfff8e3ff8ff8ffff

def z88 : W := mkw 0x30002800a0024000 0x00c000a002800900 0xf0003c00f003f03b 0x33c000f003c00fc0

def z89 : W := mkw 0x0001000410101100 0x0000040010404044 0x0000000030307301 0x2000000000c0c1cc

def z90 : W := mkw 0x702d28b4f0f6f761 0x15c0b4a2d3c3dbdd 0xf03f3cfcf1fffffb 0xf7c0fcf3f3c7ffff

def z91 : W := mkw 0x00cb452d56fdbfe0 0x20032d14b55bf6ff 0x01c7cf1fffffffdf 0xe4071f3c7fffffff

def z92 : W := mkw 0x8fd2d74b0b412c02 0xca3f4b5d2c2d04b0 0x0fc0c3030fc00c04 0x483f030c0c3f0030

def z93 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e3830e0ce038020 0x0838e0c383380e00

def z94 : W := mkw 0x0001000410101100 0x0000040010404044 0x00070c1c3030731b 0xa4001c3070c0c1cc

def z95 : W := mkw 0x0208126242218a80 0x200820498908862a 0x003833e3c0338ff3 0xa400e0cf8f00ce3f

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000030300000fc2 0x2400000c0c00003f

def z97 : W := mkw 0xe9e66d9900000002 0x8fa799b664000000 0xf1c70c1c00000008 0x13c71c3070000000

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e000000ce000035 0x4838000003380000

def z99 : W := mkw 0x502d00b4f032d301 0x1540b402d3c0cb4c 0x003f00fcf033f301 0xa400fc03f3c0cfcc

def z100 : W := mkw 0xff3cbad2ed280006 0x9ffcf2eb4bb4a000 0xfe3830e0ce000020 0x1bf8e0c383380000

def z101 : W := mkw 0xbb003a00ab034800 0x4aec00e802ac0d20 0xfe003300ce038c37 0x7bf800cc03380e30

def z102 : W := mkw 0x0083400d10941160 0x00020d0034425045 0x0007c01f003c03c0 0x84001f007c00f00f

def z103 : W := mkw 0x0040050d00403560 0x00010014340100d5 0x00000f1f00007fc2 0x2400003c7c0001ff

def z104 : W := mkw 0xbbc27f09ab436c00 0x4aef09fc26ad0db0 0xffc7ff1fffc3fc3f 0xffff1ffc7fff0ff0

def z105 : W := mkw 0xb9402d00a9426400 0x4ae500b402a50990 0xf1c00c0031c07008 0x13c7003000c701c0

def z106 : W := mkw 0xbb403fb4ab43ff01 0x4eed00fed2ad0ffc 0xffc03ffcffc3ff3f 0x7fff00fff3ff0ffc

def z107 : W := mkw 0xbb003a00ab034800 0x4aec00e802ac0d20 0xfe003c00fe03f03b 0x3bf800f003f80fc0

def z108 : W := mkw 0xbbc37f0dbbd77d60 0x4aef0dfc36ef5df5 0xffc7ff1fffffffff 0xffff1ffc7fffffff

def z109 : W := mkw 0xffffff0dffff7d64 0xdbfffffc37fffdf5 0xffffff1fffffffff 0xfffffffc7fffffff

def z110 : W := mkw 0x200028b40002d301 0x048000a2d0000b4c 0x00003cfc0003f302 0x240000f3f0000fcc

def z111 : W := mkw 0x069bd26f56bd9be0 0x201a6f49bd5af66f 0x0e3ff3ffce3f8ff7 0xec38ffcfff38fe3f

def z112 : W := mkw 0xbb403f00ab034800 0x4aed00fc02ac0d20 0xffc03f00ce03803e 0x1bff00fc03380e00

def z113 : W := mkw 0x502d00b4f0309301 0x1540b402d3c0c24c 0xf03f00fcf0300339 0x97c0fc03f3c0c00c

def z114 : W := mkw 0x99090000fdbc0004 0x1264240003f6f000 0xffc00000fffc003d 0x5bff000003fff000

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z116 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c70c1c31c07008 0x00071c3070c701c0

def z117 : W := mkw 0x9d188000ed280000 0x0274620003b4a000 0xfff8c000fffc003d 0xdbffe30003fff000

def z118 : W := mkw 0x502d0000f0300000 0x1140b40003c0c000 0xf03f0000f0300039 0x93c0fc0003c0c000

def z119 : W := mkw 0x62643fdb00000002 0x0d8990ff6c000000 0xf03f3fff0000003a 0x97c0fcfffc000000

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c0000031c0001d 0x4007000000c70000

def z121 : W := mkw 0x2658bf62466bee80 0x689962fd8919afba 0x0e38ffe3ce3ffff7 0xec38e3ff8f38ffff

def z122 : W := mkw 0xeff6ffdb02436c02 0xcfbfdbff6c090db0 0xffffffff0003fc3e 0xbffffffffc000ff0

def z123 : W := mkw 0x065897624669ae80 0x2019625d8919a6ba 0x0ff8ffe3ffffffff 0xec3fe3ff8fffffff

def z124 : W := mkw 0x0001000410941160 0x0000040010425045 0x00000000003c03c0 0x000000000000f00f

def z125 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03830e0f033f321 0x33c0e0c383c0cfcc

def z126 : W := mkw 0x0200124200000000 0x0008004908000000 0x000033e300000002 0x040000cf8c000000

def z127 : W := mkw 0xab403f000b436c00 0x4aad00fc002d0db0 0x0fc03f000fc3fc06 0x683f00fc003f0ff0

def z128 : W := mkw 0x0001000010100000 0x0000040000404000 0x0007000030300019 0x80001c0000c0c000

def z129 : W := mkw 0x0040050900402460 0x0001001424010091 0x0000030300000cc0 0x0000000c0c000033

def z130 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xfe003f00ce03fc22 0x3bf800fc03380ff0

def z131 : W := mkw 0x763cbaf2e62bca81 0x35d8f2ebcb98af2a 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z132 : W := mkw 0x0610924206090880 0x2018424908182422 0x0e00c3030e0c0cc4 0x4838030c0c383033

def z133 : W := mkw 0xe9e66d9900000002 0x8fa799b664000000 0xf1ff3cfc0000003a 0x97c7fcf3f0000000

def z134 : W := mkw 0xedf6eddb00000002 0x8fb7dbb76c000000 0xf1ffccff00000008 0x97c7ff33fc000000

def z135 : W := mkw 0xc9a6400000000000 0x8326990000000000 0xf1c7000000000008 0x13c71c0000000000

def z136 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc0ff03ffffffff 0xffff03fc0fffffff

def z137 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff003c0fff 0xfffffffffc00f03f

def z138 : W := mkw 0x0200120002010800 0x0008004800080420 0x0000330000038c02 0x200000cc00000e30

def z139 : W := mkw 0xebe67f9900000002 0x8faf99fe64000000 0xffc73f1c0000003e 0x1bff1cfc70000000

def z140 : W := mkw 0x0083400d10941160 0x00020d0034425045 0x0007c31f003c0fd7 0xe4001f0c7c00f03f

def z141 : W := mkw 0xdfbfd262ffbd8a84 0xb37eff498bfef62a 0xfffff3e3ffff8fff 0xffffffcf8ffffe3f

def z142 : W := mkw 0x22403fff0002d303 0x0c8900fffc000b4c 0x00003fff0003f302 0x240000fffc000fcc

def z143 : W := mkw 0x0208122046298a80 0x200820488118a62a 0x0e003300ce3f8ff7 0x683800cc0338fe3f

def z144 : W := mkw 0x70ef6dbdf0f6f761 0x15c3bdb6f7c3dbdd 0xf1ff3cfcf1f3f33b 0xb7c7fcf3f3c7cfcc

def z145 : W := mkw 0xbf58bf00ef6b6c00 0x4afd62fc03bdadb0 0xfff8ff00fffffc3f 0xfbffe3fc03fffff0

def z146 : W := mkw 0xeff7ffdf10d43562 0x8fbfdfff7c4350d5 0xffffffff31fc7fff 0xfffffffffcc7f1ff

def z147 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e3830e0ce338333 0xac38e0c38338ce0c

def z148 : W := mkw 0xb9c36d0db9d67560 0x4ae70db436e759d5 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z149 : W := mkw 0xfbe77f00bbd76c04 0xdbef9dfc02ef5db0 0xffc73f00ffc3fc3f 0x7bff1cfc03ff0ff0

def z150 : W := mkw 0x8fd2d74b00000002 0x8a3f4b5d2c000000 0x0fc0c30300000004 0x083f030c0c000000

def z151 : W := mkw 0x2000289400025101 0x048000a250000944 0x00000c1c00007000 0x00000030700001c0

def z152 : W := mkw 0xeffefffb46298a82 0xafbffbffed18a62a 0xffffffffce3f8fff 0xffffffffff38fe3f

def z153 : W := mkw 0x702c28b0e022c201 0x15c0b0a2c3808b08 0xf03830e0c0038020 0x13c0e0c383000e00

def z154 : W := mkw 0xef74bfdb00000002 0x8fbdd2ff6c000000 0xfe383fff00000022 0x1ff8e0fffc000000

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0x00070c1c0000001a 0x84001c3070000000

def z156 : W := mkw 0xfdbfe890fdbc0004 0x97f6ffa243f6f000 0xfffffcfcfffc003f 0xdffffff3f3fff000

def z157 : W := mkw 0x0418800044280000 0x001062000110a000 0x0e380000ce000020 0x0838e00003380000

def z158 : W := mkw 0x722d3ab4f233db01 0x15c8b4ead3c8cf6c 0xfe3f3ffcfe33ff3f 0xfff8fcfff3f8cffc

def z159 : W := mkw 0x0610924206090880 0x2018424908182422 0x0e38f3e30e0c0cf6 0xcc38e3cf8c383033

def z160 : W := mkw 0x22403f0d02437d60 0x488900fc34090df5 0x00003f1f0003ffc2 0x240000fc7c000fff

def z161 : W := mkw 0x44bfc00d54bc1164 0x9112ff003552f045 0x003fc01f003c03c0 0x8400ff007c00f00f

def z162 : W := mkw 0xddbfc000ffff6c04 0xd376ff0003fffdb0 0xffffc000fffffc3d 0xfbffff0003fffff0

def z163 : W := mkw 0xddffc50dfdfc3564 0x9377ff1437f7f0d5 0xffffcc1cfffc703d 0xdbffff3073fff1c0

def z164 : W := mkw 0xddffc509fdfc2464 0x9377ff1427f7f091 0xffffc303fffc0cfd 0xdbffff0c0ffff033

def z165 : W := mkw 0x00c2450900000000 0x0003091424000000 0x01c0c30300000004 0x0007030c0c000000

def z166 : W := mkw 0xeff6ffdb00402402 0x8fbfdbff6c010090 0xffffffff31c07c3f 0xfffffffffcc701f0

def z167 : W := mkw 0x70af68bdf0b6d361 0x15c2bda2f7c2db4d 0xf03ffcfff03ff3fb 0xb7c0fff3ffc0ffcf

def z168 : W := mkw 0x46b6d2db00000002 0x851adb4b6c000000 0x0e3ff3ff00000036 0x8c38ffcffc000000

def z169 : W := mkw 0x2650bfdb00000002 0x0c9942ff6c000000 0x0e38ffff00000036 0x8c38e3fffc000000

def z170 : W := mkw 0x702d28b4fdbed305 0x15c0b4a2d3f6fb4c 0xf03f3cfcfffff33b 0xf7c0fcf3f3ffffcc

def z171 : W := mkw 0xb9c36d0db9d67560 0x4ae70db436e759d5 0xf1c7cf1f31fc7fdf 0xf7c71f3c7cc7f1ff

def z172 : W := mkw 0xbfd2ff4bab436c02 0xcaff4bfd2ead0db0 0xffc0ff03ffc3fc3f 0x7bff03fc0fff0ff0

def z173 : W := mkw 0x16189262ef6bee80 0x605862498bbdafba 0x0e38f3e3fffffff7 0xec38e3cf8fffffff

def z174 : W := mkw 0x0001000410101100 0x0000040010404044 0x00070c1c30007008 0x00001c3070c001c0

def z175 : W := mkw 0x4024009000000000 0x0500900240000000 0x003f00fc00000000 0x8400fc03f0000000

def z176 : W := mkw 0xddbfc024fdbed305 0x9376ff0093f6fb4c 0xffffc000fffff33d 0xfbffff0003ffffcc

def z177 : W := mkw 0x726d3fb4f273ff01 0x5dc9b4fed3c9cffc 0xf03f3ffcf033ff3b 0xb7c0fcfff3c0cffc

def z178 : W := mkw 0xb9402d00a9426400 0x4ae500b402a50990 0xf1c00f0031c07c1f 0x73c7003c00c701f0

def z179 : W := mkw 0x44f6c5db00000002 0x8513db176c000000 0x01ffcfff0000001e 0x8407ff3ffc000000

def z180 : W := mkw 0x22403fdf00403562 0x0c8900ff7c0100d5 0x00003fff00007fc2 0x240000fffc0001ff

def z181 : W := mkw 0xeff6ffdb06090882 0xafbfdbff6c182422 0xffffffff0e0c0cfe 0xdffffffffc383033

def z182 : W := mkw 0xdf3c9262ef298a84 0xb37cf2498bbca62a 0xfe38f3e3ce3f8ff7 0xfff8e3cf8f38fe3f

def z183 : W := mkw 0x6634bad200000000 0x0598d2eb48000000 0xfe3fffff0000003e 0x9ff8fffffc000000

def z184 : W := mkw 0xfffefffbef6bee82 0xeffffbffefbdafba 0xffffffffffffffff 0xffffffffffffffff

def z185 : W := mkw 0x9f189262ef298a80 0x227c62498bbca62a 0xfff8f3e3ffff8fff 0xffffe3cf8ffffe3f

def z186 : W := mkw 0x0000002000008200 0x0000000080000208 0x000030e000038302 0x240000c380000e0c

def z187 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0038f3e3003f8fc2 0xa400e3cf8c00fe3f

def z188 : W := mkw 0xcdf7c50d10d43560 0x8337df14344350d5 0xffffcf1f31fc7fff 0xffffff3c7cc7f1ff

def z189 : W := mkw 0x0008002046298a80 0x200020008118a62a 0x00000000ce038000 0x0000000003380e00

def z190 : W := mkw 0xddb7c000bd9c0004 0x9376df0002f67000 0xffc7c0003fcc000c 0x5bff1f0000ff3000

def z191 : W := mkw 0x22003af60203db81 0x248800ebd8080f6e 0x00003fff0003ffc2 0x240000fffc000fff

def z192 : W := mkw 0xdf3c9262ef298a84 0xb37cf2498bbca62a 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z193 : W := mkw 0xdfffd700fffd2c04 0xdb7fff5c03fff4b0 0xffffc300fffc0c3d 0xdbffff0c03fff030

def z194 : W := mkw 0x10cb452df0f6f761 0x10432d14b7c3dbdd 0x01c7cf1ff1ffffdf 0xe4071f3c7fc7ffff

def z195 : W := mkw 0x602d28b45032d301 0x1580b4a2d140cb4c 0x003f3cfc0033f302 0xa400fcf3f000cfcc

def z196 : W := mkw 0xff3cba00ef2b4804 0xdbfcf2e803bcad20 0xfe383000ce038020 0x1bf8e0c003380e00

def z197 : W := mkw 0x0008002040208200 0x0000200081008208 0x00000000c0338301 0x200000000300ce0c

def z198 : W := mkw 0xf9af68b4f9b6d305 0x97e6bda2d3e6db4c 0xf1ff3cfcf1f3f33b 0xb7c7fcf3f3c7cfcc

def z199 : W := mkw 0xd9a74000b9940004 0x93669d0002e65000 0xf1c7000031c00008 0x13c71c0000c70000

def z200 : W := mkw 0x00c2450900c42460 0x0003091424031091 0x01c0cf0331cc7cdf 0x6007033c0cc731f3

def z201 : W := mkw 0xeff6ff0000000000 0x8bbfdbfc00000000 0xffffff000000003e 0x9bfffffc00000000

def z202 : W := mkw 0xebe67fdb00000002 0x8faf99ff6c000000 0xf1c73fff0000000a 0x17c71cfffc000000

def z203 : W := mkw 0x12001200ab436c00 0x4048004802ad0db0 0x0e003300ffc3fc37 0x683800cc03ff0ff0

def z204 : W := mkw 0x2658bffb46298a82 0x2c9962ffed18a62a 0x0e38ffffce3f8ff7 0xec38e3ffff38fe3f

def z205 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e3833e3ce038fe2 0x2c38e0cf8f380e3f

def z206 : W := mkw 0x443d80f654389381 0x3510f603d950e24e 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z207 : W := mkw 0xbf18ba62ef2bca80 0x6afc62e98bbcaf2a 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z208 : W := mkw 0x8f5097420f492c80 0x6a3d425d083d24b2 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z209 : W := mkw 0x66f6ffdb00000002 0x8d9bdbff6c000000 0x003fffff00000002 0x8400fffffc000000

def z210 : W := mkw 0x10090000ffff6c04 0x5040240003fffdb0 0x00000000fffffc01 0x6000000003fffff0

def z211 : W := mkw 0x8b4017000b412c00 0x4a2d005c002d04b0 0x0fc00f003fc07c1f 0x683f003c00ff01f0

def z212 : W := mkw 0x0200120002010800 0x0008004800080420 0x0e00f303ce3f8ff7 0xec3803cc0f38fe3f

def z213 : W := mkw 0xddbfc020fdbc8204 0x9376ff0083f6f208 0xfffff0e0ffff833f 0xffffffc383fffe0c

def z214 : W := mkw 0x06d3d74f10d43560 0x001b4f5d3c4350d5 0x0fffffff31fc7fff 0xec3ffffffcc7f1ff

def z215 : W := mkw 0x20c36dbd10d6f761 0x04830db6f4435bdd 0x01c7ffff31ffffdf 0xe4071ffffcc7ffff

def z216 : W := mkw 0xff34bad2ab034802 0xcffcd2eb4aac0d20 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z217 : W := mkw 0x70242890a0024000 0x05c090a242800900 0xf03f3cfcf003f03b 0xb7c0fcf3f3c00fc0

def z218 : W := mkw 0xe9e66d9900000002 0x8fa799b664000000 0xf1c7cf1f0000001e 0x97c71f3c7c000000

def z219 : W := mkw 0xeff6ffdb00c42462 0x8fbfdbff6c031091 0xffffffff01cc0cfe 0xdffffffffc073033

def z220 : W := mkw 0x30002800a0024000 0x00c000a002800900 0xf0003000c0038020 0x13c000c003000e00

def z221 : W := mkw 0x0001000410d43560 0x00000400104350d5 0x0000000031fc7fc1 0x6000000000c7f1ff

def z222 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c70f1c31c07c1f 0x60071c3c70c701f0

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c000003c0015 0xc00003000000f000

def z224 : W := mkw 0xddffc50dfdfc3564 0x9377ff1437f7f0d5 0xffffcf1ffffc7fff 0xffffff3c7ffff1ff

def z225 : W := mkw 0x10090004fdfc3564 0x1040240013f7f0d5 0x00000000fffc7fc1 0x6000000003fff1ff

def z226 : W := mkw 0x10400500ab436c00 0x4041001402ad0db0 0x01c00f00ffc3fc1f 0x6007003c03ff0ff0

def z227 : W := mkw 0xcfb6d24200000000 0x833edb4908000000 0xfffff3e30000003e 0x9fffffcf8c000000

def z228 : W := mkw 0xfffffffff032d303 0x9fffffffffc0cb4c 0xfffffffff033f33f 0xbfffffffffc0cfcc

def z229 : W := mkw 0x0083400d10941160 0x00020d0034425045 0x01c7c01f31fc03dd 0xc4071f007cc7f00f

def z230 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffff3cfc00000028 0x1bfffcf3f0000000

def z231 : W := mkw 0x702d28b4f63bdb81 0x35c0b4a2d3d8ef6e 0xf03f3cfcfe3ffffb 0xf7c0fcf3f3f8ffff

def z232 : W := mkw 0x8fdad76b46298a82 0xaa3f6b5dad18a62a 0x0ff8f3e3ce3f8ff7 0xec3fe3cf8f38fe3f

def z233 : W := mkw 0x10000000a9000000 0x0040000002a40000 0x00000000ffc00001 0x4000000003ff0000

def z234 : W := mkw 0x0208126246298a80 0x200820498918a62a 0x000033e3ce3f8fc3 0x640000cf8f38fe3f

def z235 : W := mkw 0xfbef7fbdfbf7ff61 0x5fefbdfef7efdffd 0xffffffffffffffff 0xffffffffffffffff

def z236 : W := mkw 0xf9652d94b9527501 0x5fe594b652e549d4 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z237 : W := mkw 0x00c2450900c42460 0x0003091424031091 0x01c7cf1f01cc0cde 0xc4071f3c7c073033

def z238 : W := mkw 0x0083400010940000 0x00020d0000425000 0x01c7000031c00008 0x00071c0000c70000

def z239 : W := mkw 0x8fd2d74b00000002 0x8a3f4b5d2c000000 0x0fc7cf1f0000001e 0x8c3f1f3c7c000000

def z240 : W := mkw 0x6024289000000000 0x058090a240000000 0xf0070c1c00000008 0x13c01c3070000000

def z241 : W := mkw 0xd9a74000b9940004 0x93669d0002e65000 0xffc70000ffc0003d 0x5bff1c0003ff0000

def z242 : W := mkw 0xedf6ed9900000002 0x8fb7dbb664000000 0xffffcc1c0000003c 0x9bffff3070000000

def z243 : W := mkw 0xbb403f00a9426400 0x4aed00fc02a50990 0xffc03f0031c0703e 0x1bff00fc00c701c0

def z244 : W := mkw 0x0240174b00000002 0x0809005d2c000000 0x0000030300000000 0x0000000c0c000000

def z245 : W := mkw 0x663cbaf246298a80 0x2598f2ebc918a62a 0xfe3fffffce3f8fff 0xfff8ffffff38fe3f

def z246 : W := mkw 0x10010004b0125101 0x1040040012c04944 0x0000000030007000 0x0000000000c001c0

def z247 : W := mkw 0x0008002040208200 0x0000200081008208 0x003800e000300300 0x8400e0038000c00c

def z248 : W := mkw 0x10090024f63bdb81 0x3040240093d8ef6e 0x00000000fe3fffc1 0x6000000003f8ffff

def z249 : W := mkw 0x70252894b0125101 0x15c094a252c04944 0xf0073c1cf003f03b 0x33c01cf073c00fc0

def z250 : W := mkw 0x00c2450900000000 0x0003091424000000 0x01c70c1c00000008 0x00071c3070000000

def z251 : W := mkw 0xddbfc062fdbc8284 0xb376ff018bf6f20a 0xffffc0e3fffc03fd 0xdfffff038ffff00f

def z252 : W := mkw 0x402c00b040208201 0x1500b002c1008208 0x003800e000000000 0x0000e00380000000

def z253 : W := mkw 0x64b6e8db00000002 0x8592dba36c000000 0xf03ffcff0000003a 0x97c0fff3fc000000

def z254 : W := mkw 0x8f10924200000002 0x8a3c424908000000 0x0e00000000000000 0x0838000000000000

def z255 : W := mkw 0x0000000000402400 0x0000000000010090 0x0000000031c07c01 0x6000000000c701f0

def z256 : W := mkw 0x0001000410101100 0x0000040010404044 0x0007cf1f303c7fdf 0xe4001f3c7cc0f1ff

def z257 : W := mkw 0xffbffaf6ffbfdb85 0xb7feffebdbfeff6e 0xffffffffffffffff 0xffffffffffffffff

def z258 : W := mkw 0xb9002800a9024000 0x02e400a002a40900 0xffc03c00ffc3f03f 0x7bff00f003ff0fc0

def z259 : W := mkw 0xd9a74000b9940004 0x93669d0002e65000 0xf1c7c00031fc001d 0xd3c71f0000c7f000

def z260 : W := mkw 0xff74bfd2ab436c02 0xcffdd2ff4aad0db0 0xfff83fe0ffc3fc3f 0x7bffe0ff83ff0ff0

def z261 : W := mkw 0x502d0004f0301100 0x1140b40013c0c044 0xf03f0c1cf030733b 0xb7c0fc3073c0c1cc

def z262 : W := mkw 0x10000000a0024000 0x0040000002800900 0x00000000f003f001 0x2000000003c00fc0

def z263 : W := mkw 0x22003ad200000002 0x0c8800eb48000000 0x000030e000000000 0x000000c380000000

def z264 : W := mkw 0xfff7ffdfb0125103 0x9fffdfff7ec04944 0xffffffff3000703e 0x9ffffffffcc001c0

def z265 : W := mkw 0x0083400d10941160 0x00020d0034425045 0x0007cc1f303c73db 0xa4001f307cc0f1cf

def z266 : W := mkw 0xbf58bf62ef6bee80 0x6afd62fd8bbdafba 0xfff83fe0ffc3fc3f 0x7bffe0ff83ff0ff0

def z267 : W := mkw 0x10090024f0f6f761 0x1040240093c3dbdd 0x00000000f1ffffc1 0x6000000003c7ffff

def z268 : W := mkw 0xfdbfe8b0fdbec205 0x97f6ffa2c3f6fb08 0xfffff0e0ffff803d 0xdbffffc383fffe00

def z269 : W := mkw 0xdd3c8000ed280004 0x9374f20003b4a000 0xfff80000ffc0003d 0x5bffe00003ff0000

def z270 : W := mkw 0x0008002046298a80 0x200020008118a62a 0x0000c303ce3f8fd7 0xe400030c0f38fe3f

def z271 : W := mkw 0x02c3570d12d53d60 0x000b0d5c344b54f5 0x0fc7ff1fffffffff 0xec3f1ffc7fffffff

def z272 : W := mkw 0xfb6d3fb4f032d301 0x1fedb4fed3c0cb4c 0xffff3ffcf033f33f 0xbffffcfff3c0cfcc

def z273 : W := mkw 0x702d2894f0325101 0x15c0b4a253c0c944 0xf03f0c1cf0307039 0x93c0fc3073c0c1c0

def z274 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7c31f01fc0fc4 0xc4071f0c7c07f03f

def z275 : W := mkw 0xf9e76d9db0125103 0x9fe79db676c04944 0xf1c70c1c30007008 0x13c71c3070c001c0

def z276 : W := mkw 0x44bfc0ff50309303 0x9512ff03fd40c24c 0x003fc0ff00300300 0x8400ff03fc00c00c

def z277 : W := mkw 0x6025289410101100 0x058094a250404044 0xf03f3cfc3030733b 0xb7c0fcf3f0c0c1cc

def z278 : W := mkw 0xbf50bf42ab436c00 0x4afd42fd0aad0db0 0xfff8ffe3ffc3fc3f 0xffffe3ff8fff0ff0

def z279 : W := mkw 0x99000000ab436c00 0x4264000002ad0db0 0xffc00000ffc3fc3d 0x7bff000003ff0ff0

def z280 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf003f028 0x13c0fcf3f3c00fc0

def z281 : W := mkw 0x0000000000c42460 0x0000000000031091 0x0000000001cc0cc0 0x4000000000073033

def z282 : W := mkw 0x200828b44022d301 0x048020a2d1008b4c 0x00383cfcc033f333 0xa400e0f3f300cfcc

def z283 : W := mkw 0xfb643f90ab436c00 0x4fed90fe42ad0db0 0xffff3ffcffc3fc3f 0xfffffcfff3ff0ff0

def z284 : W := mkw 0x0041050410d43560 0x00010414104350d5 0x01c00f0031fc7fdf 0x6007003c00c7f1ff

def z285 : W := mkw 0xeff7ffdf10941162 0x8fbfdfff7c425045 0xffffffff003c03fe 0x9ffffffffc00f00f

def z286 : W := mkw 0xdfbfd242ffbd0884 0xb37eff490bfef422 0xffffc303fffc0cfd 0xdbffff0c0ffff033

def z287 : W := mkw 0x8d92c00000000000 0x82364b0000000000 0x0fc0c00000000004 0x083f030000000000

def z288 : W := mkw 0x300028b4a002d301 0x04c000a2d2800b4c 0xf0003cfcf003f33b 0x37c000f3f3c00fcc

def z289 : W := mkw 0x04dbc56f54fcb7e0 0x20136f15bd53f2df 0x01ffcfff31fc7fdf 0xe407ff3ffcc7f1ff

def z290 : W := mkw 0x20402d0000426400 0x488100b400010990 0x00000c0000007000 0x00000030000001c0

def z291 : W := mkw 0xeff6fffb02018a82 0xafbfdbffec08062a 0xffffffff00038ffe 0xbffffffffc000e3f

def z292 : W := mkw 0x10010000b9940004 0x1040040002e65000 0x0000000031c00000 0x0000000000c70000

def z293 : W := mkw 0x10000000a0000000 0x0040000002800000 0xf0000000f0000039 0x13c0000003c00000

def z294 : W := mkw 0x8900000009000000 0x0224000000240000 0x0fc000000fc00004 0x483f0000003f0000

def z295 : W := mkw 0x0610924202010800 0x0018424908080420 0x0e38f3e3ce038c37 0xec38e3cf8f380e30

def z296 : W := mkw 0xbf18ba62ef2bca80 0x6afc62e98bbcaf2a 0xfe38f3e3ce3f8ff7 0xfff8e3cf8f38fe3f

def z297 : W := mkw 0x0492c000048c0004 0x80124b0000123000 0x0000c000000c0000 0x0000030000003000

def z298 : W := mkw 0x0618924246290880 0x201862490918a422 0x0e38c303ce3c0cf5 0xc838e30c0f38f033

def z299 : W := mkw 0xbb413f04bb537d00 0x4aed04fc12ed4df4 0xffc73f1cfff3ff3f 0xffff1cfc73ffcffc

def z300 : W := mkw 0xddbfc004fdbc1104 0x9376ff0013f6f044 0xffffcc1cfffc733f 0xffffff3073fff1cc

def z301 : W := mkw 0xcdf6c50900000000 0x8337db1424000000 0xffffcf1f0000003e 0x9fffff3c7c000000

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003000c0038033 0x200000c003000e00

def z303 : W := mkw 0x0083400010940000 0x00020d0000425000 0x01c7c30331fc0fdf 0xe4071f0c0cc7f03f

def z304 : W := mkw 0x8fd2d7000fcd2c04 0xca3f4b5c003f34b0 0x0fc0c3000fcc0c04 0x483f030c003f3030

def z305 : W := mkw 0x0418802046298a80 0x201062008118a62a 0x0e38c000ce3f8ff5 0xe838e3000338fe3f

def z306 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03ffffff03fffff 0xf7c0ffffffc0ffff

def z307 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f0e0ce3f8035 0xc838e3c38338fe00

def z308 : W := mkw 0x2000280000024000 0x008000a000000900 0x00003c000003f002 0x200000f000000fc0

def z309 : W := mkw 0x049bc00054bc0000 0x00126f000152f000 0x0fffc000fffc003d 0xc83fff0003fff000

def z310 : W := mkw 0x8940050009402400 0x4a25001400250090 0x01c0000001c00000 0x0007000000070000

def z311 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x0007cf1f003c7fc2 0xa4001f3c7c00f1ff

def z312 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffff0000ffc00028 0x1bfffc0003ff0000

def z313 : W := mkw 0x0082400000840000 0x0002090000021000 0x01c0c00001cc0004 0x4007030000073000

def z314 : W := mkw 0x06d3d74f16dd3de0 0x201b4f5d3c5b74f7 0x0fc7cf1f3ffc7fdf 0xec3f1f3c7cfff1ff

def z315 : W := mkw 0x743da8b4f43ad301 0x15d0f6a2d3d0eb4c 0xfe3ffcfcfe3ff33f 0xfff8fff3f3f8ffcc

def z316 : W := mkw 0xffffffdbffff6c06 0xdfffffff6ffffdb0 0xfffffffffffffc3f 0xfffffffffffffff0

def z317 : W := mkw 0xbb403fdbab436c02 0x4eed00ff6ead0db0 0xffc03fffffc3fc3f 0x7fff00ffffff0ff0

def z318 : W := mkw 0x0009002456fdbfe0 0x20002400915bf6ff 0x00000000ffffffc1 0x6000000003ffffff

def z319 : W := mkw 0xd9af4000f9b40004 0x9366bd0003e6d000 0xf1ff0000f1f00039 0x93c7fc0003c7c000

def z320 : W := mkw 0xbb483f20ef6bee80 0x6aed20fc83bdafba 0xffc03f00ffffffff 0x7bff00fc03ffffff

def z321 : W := mkw 0x0083400010940000 0x00020d0000425000 0x01c7c00031fc001d 0xc0071f0000c7f000

def z322 : W := mkw 0xcdbfc0005dbc0004 0x9336ff000176f000 0x0fffc0000ffc0004 0xc83fff00003ff000

def z323 : W := mkw 0x402d00b450309301 0x1500b402d140c24c 0x003f00fc00300300 0x8400fc03f000c00c

def z324 : W := mkw 0x10080020e022c201 0x1040200083808b08 0x00000000c0038000 0x0000000003000e00

def z325 : W := mkw 0xab403f0002436c00 0x4aad00fc00090db0 0xffc03f000003fc3e 0x3bff00fc00000ff0

def z326 : W := mkw 0xef34bad200000002 0x8fbcd2eb48000000 0xfe3f3cfc0000003a 0x9ff8fcf3f0000000

def z327 : W := mkw 0x0240170002412c00 0x0009005c000904b0 0x0fc03f00ffc3fc3f 0x683f00fc03ff0ff0

def z328 : W := mkw 0x200128b41012d301 0x048004a2d0404b4c 0x00073cfc3033f31b 0xa4001cf3f0c0cfcc

def z329 : W := mkw 0x10090020ffbd8a84 0x3040240083fef62a 0x00000000ffff8fc1 0x6000000003fffe3f

def z330 : W := mkw 0xd92d0000f9300000 0x1364b40003e4c000 0xffff0000fff0003d 0xdbfffc0003ffc000

def z331 : W := mkw 0x0000000400001100 0x0000000010000044 0x00000c1c00007302 0x24000030700001cc

def z332 : W := mkw 0xefb6fadb00000002 0x8fbedbeb6c000000 0xfe3ff0ff00000020 0x9ff8ffc3fc000000

def z333 : W := mkw 0x60e66d9900000000 0x058399b664000000 0xf1ffffff0000003e 0x97c7fffffc000000

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x003830e000000032 0x8400e0c380000000

def z335 : W := mkw 0x2000289000000000 0x048000a240000000 0x00003cfc00000002 0x040000f3f0000000

def z336 : W := mkw 0xab403f000b412c00 0x4aad00fc002d04b0 0xffc03f000fc00c3e 0x5bff00fc003f0030

def z337 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xf1c0000031c00008 0x13c7000000c70000

def z338 : W := mkw 0x602d28b450309301 0x1580b4a2d140c24c 0xf03f3cfc0030033a 0x97c0fcf3f000c00c

def z339 : W := mkw 0xfb2d3ab4fb33db01 0x5fecb4ead3eccf6c 0xfe3f3cfcfe33f33b 0xbff8fcf3f3f8cfcc

def z340 : W := mkw 0x32003a00a2034800 0x00c800e802880d20 0xfe003f00fe03fc3f 0x7bf800fc03f80ff0

def z341 : W := mkw 0xeffefffb44288282 0xafbffbffed10a20a 0xffffffff003c03fe 0x9ffffffffc00f00f

def z342 : W := mkw 0xb9402d00a9426400 0x4ae500b402a50990 0xffc00c00ffc0703d 0x5bff003003ff01c0

def z343 : W := mkw 0x30092824f032d301 0x10c024a093c0cb4c 0xf0003c00f033f33b 0x33c000f003c0cfcc

def z344 : W := mkw 0x000000db00000002 0x040000036c000000 0x000000ff00000000 0x04000003fc000000

def z345 : W := mkw 0xaf58bf6246298a80 0x2abd62fd8918a62a 0xfff8ffe3ce3f8fff 0xffffe3ff8f38fe3f

def z346 : W := mkw 0x0001000410d43560 0x00000400104350d5 0x0000000031c07000 0x0000000000c701c0

def z347 : W := mkw 0xbb403f0dab437d60 0x4aed00fc36ad0df5 0xffc03f1fffc3ffff 0x7fff00fc7fff0fff

def z348 : W := mkw 0xb9402d00a9426400 0x4ae500b402a50990 0xf1c03c00f1c3f03b 0x33c700f003c70fc0

def z349 : W := mkw 0x30002800a0024000 0x00c000a002800900 0xf0000c0030007008 0x13c0003000c001c0

def z350 : W := mkw 0x9d92c000ad8c0004 0x82764b0002b63000 0xffc0c000ffcc003d 0x5bff030003ff3000

def z351 : W := mkw 0x0041050d10503560 0x00010414344140d5 0x00070f1f30307fdb 0xa4001c3c7cc0c1ff

def z352 : W := mkw 0x543d8000f4380000 0x1150f60003d0e000 0xfe3fc000fe3c003d 0xdbf8ff0003f8f000

def z353 : W := mkw 0x70252894b0125101 0x15c094a252c04944 0xf03f3cfc3000703a 0x97c0fcf3f0c001c0

def z354 : W := mkw 0x0040050d00403560 0x00010014340100d5 0x00000c1c00007000 0x00000030700001c0

def z355 : W := mkw 0xddbec000ed280004 0x9376fb0003b4a000 0xffffc000ce00003c 0x9bffff0003380000

def z356 : W := mkw 0xbfd2ff00afcf6c04 0xcaff4bfc02bf3db0 0xffc0ff00ffcffc3f 0x7bff03fc03ff3ff0

def z357 : W := mkw 0x22403fdb02436c02 0x4c8900ff6c090db0 0x00003fff0003fc02 0x240000fffc000ff0

def z358 : W := mkw 0xd9af4000fdbc0004 0x9366bd0003f6f000 0xf1c70000fffc0009 0x53c71c0003fff000

def z359 : W := mkw 0x30002800ab436c00 0x40c000a002ad0db0 0xf0003c00ffc3fc3b 0x73c000f003ff0ff0

def z360 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xfe3fc000ce3c0020 0x9bf8ff000338f000

def z361 : W := mkw 0x602c28b040208200 0x0580b0a2c1008208 0xf03f3cfcc033833b 0xb7c0fcf3f300ce0c

def z362 : W := mkw 0xcdbec00044280000 0x8336fb000110a000 0xffffc000ce3c003d 0xdbffff000338f000

def z363 : W := mkw 0xedb6e89000000000 0x87b6dba240000000 0xfffffcfc0000003e 0x9ffffff3f0000000

def z364 : W := mkw 0x8fd3d74f10d43562 0x8a3f4f5d3c4350d5 0x0fc7cf1f31fc7fdf 0xec3f1f3c7cc7f1ff

def z365 : W := mkw 0x0618920046290800 0x001862480118a420 0x0e38f300ce3f8c37 0xe838e3cc0338fe30

def z366 : W := mkw 0xcff6d7db00000002 0x8f3fdb5f6c000000 0x0fffc3ff00000004 0x8c3fff0ffc000000

def z367 : W := mkw 0xeff6ffdb0b412c02 0xcfbfdbff6c2d04b0 0xffffffff0fc00c3e 0xdffffffffc3f0030

def z368 : W := mkw 0x9d9bc000fdbc0004 0x92766f0003f6f000 0x0fc0c000fffc0005 0x483f030003fff000

def z369 : W := mkw 0x049bc06f54bc93e0 0x20126f01bd52f24f 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z370 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xfff8f3e300000024 0x1bffe3cf8c000000

def z371 : W := mkw 0x8b4017000b412c00 0x4a2d005c002d04b0 0x0fc03300cfc38c37 0x683f00cc033f0e30

def z372 : W := mkw 0xfff6ffdba9426402 0xcfffdbff6ea50990 0xffffffff31c0703e 0x9ffffffffcc701c0

def z373 : W := mkw 0xfffffffffb73ff03 0xdfffffffffedcffc 0xfffffffffff3ff3f 0xffffffffffffcffc

def z374 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f3e3ce0f8ce4 0x4838e3cf8f383e33

def z375 : W := mkw 0xddbfc0b4fdbc9305 0x9776ff02d3f6f24c 0xffffc0fcfffc033d 0xdfffff03f3fff00c

def z376 : W := mkw 0x99834000b9940000 0x02660d0002e65000 0xffc7c000fffc003d 0xdbff1f0003fff000

def z377 : W := mkw 0xf9e66d99a9426402 0xcfe799b666a50990 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z378 : W := mkw 0x000000000b412c00 0x40000000002d04b0 0x000000000fc00c00 0x40000000003f0030

def z379 : W := mkw 0x00c3450d10101100 0x00030d1434404044 0x01c7cf1f3030731f 0xa4071f3c7cc0c1cc

def z380 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc00f003fc07c0c 0x5bff003c00ff01f0

def z381 : W := mkw 0x22c37f0d12d77d60 0x488b0dfc344b5df5 0x01c7ff1f31ffffdf 0xe4071ffc7cc7ffff

def z382 : W := mkw 0x0240176f0241bfe0 0x2009005dbc0906ff 0x00003fff0003ffc2 0x240000fffc000fff

def z383 : W := mkw 0x706d2db4f072f701 0x15c1b4b6d3c1cbdc 0xf1ff3ffcf1f3ff3f 0xf7c7fcfff3c7cffc

def z384 : W := mkw 0x0008002044288280 0x200020008110a20a 0x00000000003c03c0 0x000000000000f00f

def z385 : W := mkw 0xddb7c000b9940004 0x9376df0002e65000 0xffffc00031c0003c 0x9bffff0000c70000

def z386 : W := mkw 0x40ef45bd50f4b761 0x1503bd16f543d2dd 0x01ffcfff31fc7fdf 0xe407ff3ffcc7f1ff

def z387 : W := mkw 0x44bfc0db54bc0006 0x9512ff036d52f000 0x003fc0ff003c0000 0x8400ff03fc00f000

def z388 : W := mkw 0xbbc37f00bbd76c00 0x4aef0dfc02ef5db0 0xffc7ff00fffffc3f 0xfbff1ffc03fffff0

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000c003000701b 0x2000003000c001c0

def z390 : W := mkw 0xcdb7c00010940000 0x8336df0000425000 0xffffc00031fc003d 0xdbffff0000c7f000

def z391 : W := mkw 0xeff6ffdb02010802 0x8fbfdbff6c080420 0xffffffffce038c3f 0xffffffffff380e30

def z392 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e00c303ce3f8fc5 0x6838030c0f38fe3f

def z393 : W := mkw 0x22003a0002034800 0x488800e800080d20 0x0000300000038000 0x000000c000000e00

def z394 : W := mkw 0x0418806246298a80 0x201062018918a62a 0x0038c0e3ce3f8fc1 0xe400e3038f38fe3f

def z395 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cc1f31fc73c8 0x84071f307cc7f1cf

def z396 : W := mkw 0xfff6ffdba0024002 0x8fffdbff6e800900 0xfffffffff003f03f 0xbfffffffffc00fc0

def z397 : W := mkw 0x0041050d10d43560 0x00010414344350d5 0x00000f1f31fc7fc3 0x6400003c7cc7f1ff

def z398 : W := mkw 0x563d9262f6398a80 0x3158f6498bd8e62a 0xfe3ff3e3fe3f8fff 0xfff8ffcf8ff8fe3f

def z399 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03830e000000020 0x13c0e0c380000000

def z400 : W := mkw 0x22c37fdf10d43562 0x0c8b0dff7c4350d5 0x01c7ffff31fc7fdf 0xe4071ffffcc7f1ff

def z401 : W := mkw 0x10000000ab034800 0x4040000002ac0d20 0x00000000ce038000 0x0000000003380e00

def z402 : W := mkw 0x0610924200000000 0x0018424908000000 0x0e38f3e3003c0ff7 0xec38e3cf8c00f03f

def z403 : W := mkw 0xddbfc004fdfc3564 0x9376ff0013f7f0d5 0xffffc000fffc7ffd 0xfbffff0003fff1ff

def z404 : W := mkw 0x0200120002010800 0x0008004800080420 0x0e003000ce038020 0x083800c003380e00

def z405 : W := mkw 0x0000000400403560 0x00000000100100d5 0x0000000000007fc0 0x20000000000001ff

def z406 : W := mkw 0x2000280000000000 0x008000a000000000 0xf0003c000000003a 0x13c000f000000000

def z407 : W := mkw 0x00c2450900c42460 0x0003091424031091 0x01c0000001c00000 0x0007000000070000

def z408 : W := mkw 0x99c3450db9d43560 0x02670d1436e750d5 0xffc7cf1ffffc7fff 0xffff1f3c7ffff1ff

def z409 : W := mkw 0x8bc257090bc52c60 0x4a2f095c242f14b1 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z410 : W := mkw 0xdfbfd200ffbd0804 0x937eff4803fef420 0xfffff300ffff8c3f 0xfbffffcc03fffe30

def z411 : W := mkw 0x0001000410d43560 0x00000400104350d5 0x0000c30331fc7fd7 0xe400030c0cc7f1ff

def z412 : W := mkw 0x46bed2fb46298a82 0xa51afb4bed18a62a 0x0e3ff3ffce3f8ff7 0xec38ffcfff38fe3f

def z413 : W := mkw 0xbb493f00ffff6c04 0x5aed24fc03fffdb0 0xffc03f00fffffc3f 0x7bff00fc03fffff0

def z414 : W := mkw 0x0410800000000000 0x0010420000000000 0x0e38c00000000034 0x8838e30000000000

def z415 : W := mkw 0xefffffff56fdbfe2 0xafbffffffd5bf6ff 0xffffffffffffffff 0xffffffffffffffff

def z416 : W := mkw 0x8d1080000d080004 0x8234420000342000 0x0e0000000e000000 0x0838000000380000

def z417 : W := mkw 0x10000000a9426400 0x4040000002a50990 0x0000000031c07000 0x0000000000c701c0

def z418 : W := mkw 0x44bec0fb44288282 0xa512fb03ed10a20a 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z419 : W := mkw 0x726d3ffff032d303 0x1dc9b4ffffc0cb4c 0xf03f3ffff033f33b 0xb7c0fcffffc0cfcc

def z420 : W := mkw 0xbfdbff6fffffffe0 0x6aff6ffdbfffffff 0xffffffffffffffff 0xffffffffffffffff

def z421 : W := mkw 0xfdffedbdfdfef765 0x97f7ffb6f7f7fbdd 0xffffffffffffffff 0xffffffffffffffff

def z422 : W := mkw 0xbbc27f09abc76c60 0x4aef09fc26af1db1 0xffc0ff03ffcffcff 0x7bff03fc0fff3ff3

def z423 : W := mkw 0xffffff62ffffee84 0xfbfffffd8bffffba 0xffffffe3ffffffff 0xffffffff8fffffff

def z424 : W := mkw 0x702d2800f0324000 0x11c0b4a003c0c900 0xf03f3c00f033f03b 0xb3c0fcf003c0cfc0

def z425 : W := mkw 0x0009000054bc0004 0x100024000152f000 0x00000000003c0000 0x000000000000f000

def z426 : W := mkw 0xddbfc0dbfdbc0006 0x9776ff036ff6f000 0xffffc0fffffc003d 0xdfffff03fffff000

def z427 : W := mkw 0x0418806244288280 0x201062018910a20a 0x003800e000000000 0x0000e00380000000

def z428 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e3833e0ce038c37 0x6838e0cf83380e30

def z429 : W := mkw 0x70e76d9db0d67561 0x15c39db676c359d5 0xf1c7cf1f31fc7fdf 0xf7c71f3c7cc7f1ff

def z430 : W := mkw 0x443c800044280004 0x9110f2000110a000 0x0038000000000000 0x0000e00000000000

def z431 : W := mkw 0x702c28b0e022c201 0x15c0b0a2c3808b08 0xf03f3cfcc003803a 0x97c0fcf3f3000e00

def z432 : W := mkw 0x0610924206090880 0x2018424908182422 0x0e00f303ce0f8cf7 0x683803cc0f383e33

def z433 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38c3e30e3c0fc4 0xcc38e30f8c38f03f

def z434 : W := mkw 0x60e76d9d10d43560 0x05839db6744350d5 0xf1ffffff31fc7fff 0xf7c7fffffcc7f1ff

def z435 : W := mkw 0x4025009410101101 0x1500940250404044 0x0007001c00000000 0x00001c0070000000

def z436 : W := mkw 0xff7cbf00ef6b6c04 0xdbfdf2fc03bdadb0 0xfff83f00ffc3fc3f 0x7bffe0fc03ff0ff0

def z437 : W := mkw 0x20402d9900000002 0x0c8100b664000000 0x00000c1c00000000 0x0000003070000000

def z438 : W := mkw 0xbb403f62ab43ee80 0x6aed00fd8aad0fba 0xffc03fe3ffc3ffff 0x7fff00ff8fff0fff

def z439 : W := mkw 0xafd2ff4b00000002 0x8abf4bfd2c000000 0xffc0ff030000003e 0x1bff03fc0c000000

def z440 : W := mkw 0xbb493f24fb73ff01 0x5aed24fc93edcffc 0xffc03f00fff3ff3f 0x7bff00fc03ffcffc

def z441 : W := mkw 0x702d2890f0300000 0x15c0b4a243c0c000 0xf03f3cfcf030003b 0x97c0fcf3f3c0c000

def z442 : W := mkw 0x70ef6dbdf032d301 0x15c3bdb6f7c0cb4c 0xf1fffffff033f33f 0xb7c7ffffffc0cfcc

def z443 : W := mkw 0x10080020ef6bee80 0x6040200083bdafba 0x00000000ffffffc1 0x6000000003ffffff

def z444 : W := mkw 0x0008002040208200 0x0000200081008208 0x003830e0c0038020 0x0000e0c383000e00

def z445 : W := mkw 0xeff7ffdf10101102 0x8fbfdfff7c404044 0xffffffff3030733f 0xbffffffffcc0c1cc

def z446 : W := mkw 0x443480d200000002 0x8510d20348000000 0x003800e000000000 0x0000e00380000000

def z447 : W := mkw 0xffbffad2fdbc0006 0x9ffeffeb4bf6f000 0xfffff0e0fffc003d 0xdbffffc383fff000

def z448 : W := mkw 0xddb6c000a9000000 0x8376db0002a40000 0xffffc000ffc0003d 0xdbffff0003ff0000

def z449 : W := mkw 0x00c3450910940000 0x00030d1424425000 0x01c7cf1f31fc001f 0xc4071f3c7cc7f000

def z450 : W := mkw 0xffffffdbf0300002 0x9fffffff6fc0c000 0xfffffffff030003f 0x9fffffffffc0c000

def z451 : W := mkw 0xefffffdb54bc0006 0x9fbfffff6d52f000 0xffffffff003c003e 0x9ffffffffc00f000

def z452 : W := mkw 0x0610926202018a80 0x201842498808062a 0x0e38f3e300038ff6 0xac38e3cf8c000e3f

def z453 : W := mkw 0xdd3d8000fd380004 0x9374f60003f4e000 0xfe3f0000fe300039 0x9bf8fc0003f8c000

def z454 : W := mkw 0x0492c04b00000002 0x80124b012c000000 0x0000c00300000000 0x000003000c000000

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000030000000c17 0x6000000c00000030

def z456 : W := mkw 0x0082400000000000 0x0002090000000000 0x01c7c0000000001c 0x80071f0000000000

def z457 : W := mkw 0x30082820e022c200 0x00c020a083808b08 0xf0383ce0f033f33b 0xb7c0e0f383c0cfcc

def z458 : W := mkw 0x8f9ad2624fad8a84 0xa23e6b49893eb62a 0x0ff8f3e3cfff8ff7 0xec3fe3cf8f3ffe3f

def z459 : W := mkw 0x0619926656399b80 0x201866499958e66e 0x0e3ffffffe3fffff 0xec38fffffff8ffff

def z460 : W := mkw 0x0200126202018a80 0x200800498808062a 0x0000f3e3003f8fd7 0xe40003cf8c00fe3f

def z461 : W := mkw 0x00c2450900c42460 0x0003091424031091 0x01c0c30301fc0fd7 0xe407030c0c07f03f

def z462 : W := mkw 0xfffffffbffbd8a86 0xbfffffffeffef62a 0xffffffffffff8fff 0xfffffffffffffe3f

def z463 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffc7cf1f0000000c 0x1bff1f3c7c000000

def z464 : W := mkw 0xafd2ffdb00000002 0x8ebf4bff6c000000 0x0fc0ffff00000006 0x0c3f03fffc000000

def z465 : W := mkw 0x0001000410d43560 0x00000400104350d5 0x00070c1c31fc7fdb 0xe4001c3070c7f1ff

def z466 : W := mkw 0x22403f0000000000 0x088900fc00000000 0x00003f0000000002 0x000000fc00000000

def z467 : W := mkw 0xfffffffff0f6f763 0x9fffffffffc3dbdd 0xfffffffff1ffffff 0xffffffffffc7ffff

def z468 : W := mkw 0x0000006200008280 0x200000018800020a 0x000000e3000003c0 0x040000038c00000f

def z469 : W := mkw 0x22403ffb02018a82 0x2c8900ffec08062a 0x00003fff00038fc2 0x240000fffc000e3f

def z470 : W := mkw 0xfff6ffdba9000002 0x8fffdbff6ea40000 0xffffffffffc0003f 0xdfffffffffff0000

def z471 : W := mkw 0xef3cbaf246298a82 0xafbcf2ebc918a62a 0xfe38f3e3ce3f8ff7 0xfff8e3cf8f38fe3f

def z472 : W := mkw 0x0610924200000000 0x0018424908000000 0x0e00c30300000004 0x0838030c0c000000

def z473 : W := mkw 0x0410804200000000 0x0010420108000000 0x0038c0e300000000 0x8400e3038c000000

def z474 : W := mkw 0xfd3ca8b0ed2ac205 0x97f4f2a2c3b4ab08 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z475 : W := mkw 0x0418806244288280 0x201062018910a20a 0x0e38c0e3ce3c03f5 0xcc38e3038f38f00f

def z476 : W := mkw 0x0000002002018a80 0x200000008008062a 0x0000000000038fc0 0x2000000000000e3f

def z477 : W := mkw 0xfff6ff00ab436c00 0xcbffdbfc02ad0db0 0xffffff00ffc3fc3f 0xfbfffffc03ff0ff0

def z478 : W := mkw 0x763dbaf6f63bdb81 0x35d8f6ebdbd8ef6e 0xfe3f3cfcfe33f33b 0xbff8fcf3f3f8cfcc

def z479 : W := mkw 0x0610924206090880 0x2018424908182422 0x0e00c3030e3c0fd7 0xec38030c0c38f03f

def z480 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xf1ffc00031fc0008 0x93c7ff0000c7f000

def z481 : W := mkw 0xfb2c3ab0eb23ca01 0x5fecb0eac3ac8f28 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z482 : W := mkw 0xabc27f0900000000 0x0aaf09fc24000000 0xffc7ff1f0000003e 0x9fff1ffc7c000000

def z483 : W := mkw 0x44bfc00054bc0004 0x9112ff000152f000 0x0e3fc000ce3c0035 0xc838ff000338f000

def z484 : W := mkw 0xef3cbaf246298a82 0xafbcf2ebc918a62a 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z485 : W := mkw 0x0008002046298a80 0x200020008118a62a 0x003830e0ce3f8ff3 0xe400e0c38338fe3f

def z486 : W := mkw 0x0040050000402400 0x0001001400010090 0x01c00c0031c07008 0x0007003000c701c0

def z487 : W := mkw 0x0008000044280000 0x000020000110a000 0x00000000ce3c0001 0x400000000338f000

def z488 : W := mkw 0xbb003a00ab034800 0x4aec00e802ac0d20 0xffc03000ffc3803d 0x5bff00c003ff0e00

def z489 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00070c1cf033f31b 0xa4001c3073c0cfcc

def z490 : W := mkw 0x00c2450900000000 0x0003091424000000 0x01c7cf1f003c0fdf 0xe4071f3c7c00f03f

def z491 : W := mkw 0x0083400410941100 0x00020d0010425044 0x01c7cc1c31fc731f 0xe4071f3070c7f1cc

def z492 : W := mkw 0x70252894b0125101 0x15c094a252c04944 0xf0070c1c3030731b 0xb7c01c3070c0c1cc

def z493 : W := mkw 0xfdbfe800fdbe4004 0x93f6ffa003f6f900 0xfffffc00fffff03f 0xfbfffff003ffffc0

def z494 : W := mkw 0x9b401700ab436c00 0x4a6d005c02ad0db0 0x0fc00300ffc3fc05 0x683f000c03ff0ff0

def z495 : W := mkw 0x00c2450900402400 0x0003091424010090 0x01c7cf1f31c07c1f 0xe4071f3c7cc701f0

def z496 : W := mkw 0x0008002040208200 0x0000200081008208 0x0038f3e3c03f8ff7 0xe400e3cf8f00fe3f

def z497 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f30fcc0338320 0x97c0fcc3f300ce0c

def z498 : W := mkw 0xbb003a00ab436c00 0x4aec00e802ad0db0 0xfe003000ffc3fc21 0x7bf800c003ff0ff0

def z499 : W := mkw 0x02c3576f12d5bfe0 0x200b0d5dbc4b56ff 0x01c7ffff31ffffdf 0xe4071ffffcc7ffff

def z500 : W := mkw 0x8dd3c50d1ddc3564 0x82374f14347770d5 0x0fc7cf1f3ffc7fdf 0xec3f1f3c7cfff1ff

def z501 : W := mkw 0x702d28b4fb73ff01 0x55c0b4a2d3edcffc 0xf03f3cfcfff3ff3b 0xf7c0fcf3f3ffcffc

def z502 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03300cfc38c24 0x5bff00cc033f0e30

def z503 : W := mkw 0xab003a0000000000 0x0aac00e800000000 0xfe00300000000020 0x1bf800c000000000

def z504 : W := mkw 0xfd3da8b4fd3ad305 0x97f4f6a2d3f4eb4c 0xfe3f3cfcfe33f33b 0xbff8fcf3f3f8cfcc

def z505 : W := mkw 0x0410800004080000 0x0010420000102000 0x0e00c0000e0c0004 0x4838030000383000

def z506 : W := mkw 0x00c3450910d42460 0x00030d1424435091 0x01c7c30331fc0cdd 0xc0071f0c0cc7f033

def z507 : W := mkw 0x0618926240208200 0x0018624989008208 0x0e38f3e3c0338337 0xac38e3cf8f00ce0c

def z508 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03c00ffc3f028 0x1bff00f003ff0fc0

def z509 : W := mkw 0x44b6c00000000000 0x8112db0000000000 0x003fc00000000000 0x8000ff0000000000

def z510 : W := mkw 0xfdbfe894fdbe5105 0x97f6ffa253f6f944 0xffffcc1cfffc703d 0xdbffff3073fff1c0

def z511 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf0070c1cf033f309 0x33c01c3073c0cfcc

def z512 : W := mkw 0xcff6d74b00000002 0x8b3fdb5d2c000000 0xffffc3030000003c 0x9bffff0c0c000000

def z513 : W := mkw 0x0008000040200000 0x0000200001008000 0x00380000c0300031 0x8000e0000300c000

def z514 : W := mkw 0xfb6c3fb0eb63ee01 0x5fedb0fec3ad8fb8 0xfff83fe0ffc3fc3f 0x7bffe0ff83ff0ff0

def z515 : W := mkw 0x0418800044280000 0x001062000110a000 0x0e38c303ce3c0ff7 0xec38e30c0f38f03f

def z516 : W := mkw 0xfb653f94bb537d01 0x5fed94fe52ed4df4 0xffc73f1cffc3fc3f 0x7bff1cfc73ff0ff0

def z517 : W := mkw 0x8fd2d74b00000002 0x8a3f4b5d2c000000 0x0ff8f3e300000036 0x8c3fe3cf8c000000

def z518 : W := mkw 0x502d0000fdbc0004 0x1140b40003f6f000 0xf03f0000fffc0039 0xd3c0fc0003fff000

def z519 : W := mkw 0x30c36d0db0d67560 0x00c30db436c359d5 0xf1c7ff1ff1ffffff 0xf7c71ffc7fc7ffff

def z520 : W := mkw 0xffffffb4ffffff05 0xdffffffed3fffffc 0xfffffffcffffff3f 0xfffffffff3fffffc

def z521 : W := mkw 0x000000240002d301 0x0000000090000b4c 0x000000000003f300 0x2000000000000fcc

def z522 : W := mkw 0x0618924244280000 0x001862490910a000 0x0e38f3e3ce3c0037 0xcc38e3cf8f38f000

def z523 : W := mkw 0x40af40bd50b49361 0x1502bd02f542d24d 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z524 : W := mkw 0x0418802044288200 0x001062008110a208 0x0e38f0e0ce3f8337 0xec38e3c38338fe0c

def z525 : W := mkw 0x46bfd26256bd8a84 0xb11aff49895af62a 0x0e3ff3e3ce3f8ff7 0xec38ffcf8f38fe3f

def z526 : W := mkw 0x0418800044280000 0x001062000110a000 0x0038c000003c0000 0x8000e3000000f000

def z527 : W := mkw 0xfdffed99fdbc0006 0x9ff7ffb667f6f000 0xffffcc1cfffc003d 0xdbffff3073fff000

def z528 : W := mkw 0xddbfc000f0300000 0x9376ff0003c0c000 0xffffc000f030003d 0x9bffff0003c0c000

def z529 : W := mkw 0x06dad76b46edaee0 0x201b6b5dad1bb6bb 0x0ff8f3e3cfff8ff7 0xec3fe3cf8f3ffe3f

def z530 : W := mkw 0x069bd26256bd8a80 0x201a6f49895af62a 0x0ffff3e3ffff8fff 0xec3fffcf8ffffe3f

def z531 : W := mkw 0x8fd2d74b00c42462 0x8a3f4b5d2c031091 0x0fc0c30301cc0cc4 0x483f030c0c073033

def z532 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c70c1c31fc7fc9 0x60071c3070c7f1ff

def z533 : W := mkw 0x8d93c0001d9c0004 0x82364f0000767000 0x0fc7c0003ffc001d 0xc83f1f0000fff000

def z534 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cf1f31cc7ccc 0x40071f3c7cc731f3

def z535 : W := mkw 0xf96d2db4f972f701 0x5fe5b4b6d3e5cbdc 0xf1ff3cfcf1f3f33b 0xb7c7fcf3f3c7cfcc

def z536 : W := mkw 0x402d00b450309301 0x1500b402d140c24c 0x003f30fcc0338333 0xa400fcc3f300ce0c

def z537 : W := mkw 0x702c28b4e022d301 0x15c0b0a2d3808b4c 0xf0383cfcc003f322 0x37c0e0f3f3000fcc

def z538 : W := mkw 0x0610926206098a80 0x201842498818262a 0x0e00f3e30e0f8fc6 0x6c3803cf8c383e3f

def z539 : W := mkw 0x20402dbd0042f761 0x048100b6f4010bdd 0x00003fff0003ffc2 0x240000fffc000fff

def z540 : W := mkw 0x0082400900000000 0x0002090024000000 0x0007c01f00000000 0x84001f007c000000

def z541 : W := mkw 0xdfbfd262ffbd8a84 0xb37eff498bfef62a 0xfffff0e0ffff803d 0xdbffffc383fffe00

def z542 : W := mkw 0xeffefffb46298a82 0xafbffbffed18a62a 0xffffffffce03803e 0x9fffffffff380e00

def z543 : W := mkw 0xddffc500fdfc2404 0x9377ff1403f7f090 0xffffcf00fffc7c3f 0xfbffff3c03fff1f0

def z544 : W := mkw 0x502d0024f032d301 0x1140b40093c0cb4c 0xf03f0000f033f339 0xb3c0fc0003c0cfcc

def z545 : W := mkw 0x0040050000402400 0x0001001400010090 0x01c0cf0331fc7fdf 0xe407033c0cc7f1ff

def z546 : W := mkw 0x0610924200000000 0x0018424908000000 0x0e3830e000000020 0x0838e0c380000000

def z547 : W := mkw 0x502c0000e0200000 0x1140b00003808000 0xf0380000c0000020 0x13c0e00003000000

def z548 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xf1c03f0031c3fc0a 0x33c700fc00c70ff0

def z549 : W := mkw 0xddbfc020ffbd8a84 0xb376ff0083fef62a 0xffffc000ffff8ffd 0xfbffff0003fffe3f

def z550 : W := mkw 0x44f7c5df10d43562 0x8513df177c4350d5 0x01ffcfff31fc7fdf 0xe407ff3ffcc7f1ff

def z551 : W := mkw 0x06d2d74b00000000 0x001b4b5d2c000000 0x0fffffff0000003e 0x8c3ffffffc000000

def z552 : W := mkw 0x0083400410d43560 0x00020d00104350d5 0x01c7c00031fc7fdd 0xe0071f0000c7f1ff

def z553 : W := mkw 0xff3dbaf6f032d303 0x9ffcf6ebdbc0cb4c 0xfe3f3cfcf033f33b 0xbff8fcf3f3c0cfcc

def z554 : W := mkw 0x0040050000402400 0x0001001400010090 0x01c0030001c00c04 0x4007000c00070030

def z555 : W := mkw 0x10080000ed280004 0x1040200003b4a000 0x00000000ce000000 0x0000000003380000

def z556 : W := mkw 0x0041050410503500 0x00010414104140d4 0x01c70f1c31f07f1f 0xe4071c3c70c7c1fc

def z557 : W := mkw 0xfdbfe8b4f032d301 0x97f6ffa2d3c0cb4c 0xfffffcfcf033f33f 0xbffffff3f3c0cfcc

def z558 : W := mkw 0xeff7ffdb10940002 0x8fbfdfff6c425000 0xffffffff31fc003f 0xdffffffffcc7f000

def z559 : W := mkw 0x9b001200ab010800 0x026c004802ac0420 0xffc03300ffc38c3f 0x7bff00cc03ff0e30

def z560 : W := mkw 0xbbc37f0dbbd77d60 0x4aef0dfc36ef5df5 0xffc73f1cffc3fc3f 0x7bff1cfc73ff0ff0

def z561 : W := mkw 0x70e76d9db0d67561 0x15c39db676c359d5 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z562 : W := mkw 0x722d3af6f233db81 0x35c8b4ebdbc8cf6e 0xf03f3ffff033fffb 0xb7c0fcffffc0cfff

def z563 : W := mkw 0x0000000d00001160 0x0000000034000045 0x0000001f000003c0 0x040000007c00000f

def z564 : W := mkw 0xf9e76d00b9d66404 0xdbe79db402e75990 0xf1c70c0031c07008 0x13c71c3000c701c0

def z565 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c70c1c31f0731b 0xa4071c3070c7c1cc

def z566 : W := mkw 0x9b401700ab412c00 0x4a6d005c02ad04b0 0xffc00300ffc00c3d 0x5bff000c03ff0030

def z567 : W := mkw 0x00c3450d10941160 0x00030d1434425045 0x01c7cf1f003c03de 0x84071f3c7c00f00f

def z568 : W := mkw 0x706d2dbdf072f761 0x15c1b4b6f7c1cbdd 0xf03f3ffff033fffb 0xb7c0fcffffc0cfff

def z569 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cf1f31c0701e 0x84071f3c7cc701c0

def z570 : W := mkw 0xf9ef6dbdf032d303 0x9fe7bdb6f7c0cb4c 0xf1ff3cfcf033f33b 0xb7c7fcf3f3c0cfcc

def z571 : W := mkw 0xffffffdffdfc3566 0x9fffffff7ff7f0d5 0xfffffffffffc7fff 0xfffffffffffff1ff

def z572 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f3e3ce038036 0x8c38e3cf8f380e00

def z573 : W := mkw 0x99400500a9402400 0x0265001402a50090 0xffc00f00ffc07c3f 0x7bff003c03ff01f0

def z574 : W := mkw 0x0619926656fdbfe0 0x20186649995bf6ff 0x0e38f3e3fffffff7 0xec38e3cf8fffffff

def z575 : W := mkw 0x702528b4b012d301 0x15c094a2d2c04b4c 0xf0073cfc3003f30a 0x37c01cf3f0c00fcc

def z576 : W := mkw 0x06dad76b46298a80 0x201b6b5dad18a62a 0x0fffffffce3f8fff 0xec3fffffff38fe3f

def z577 : W := mkw 0xbb483f20eb63ee00 0x4aed20fc83ad8fb8 0xfff83fe0fff3ff3f 0xffffe0ff83ffcffc

def z578 : W := mkw 0xfffffffffdbed307 0x9ffffffffff6fb4c 0xfffffffffffff33f 0xffffffffffffffcc

def z579 : W := mkw 0x0040050d00403560 0x00010014340100d5 0x0000cf1f003c7fd7 0xe400033c7c00f1ff

def z580 : W := mkw 0xd9240000a9000004 0x9364900002a40000 0xf000000000000000 0x13c0000000000000

def z581 : W := mkw 0x402d000050300000 0x1100b4000140c000 0x003f000000300000 0x8000fc000000c000

def z582 : W := mkw 0x50250000b0100000 0x1140940002c04000 0xf007000030000008 0x13c01c0000c00000

def z583 : W := mkw 0xeff6ffdf00403562 0x8fbfdbff7c0100d5 0xffffffff00007ffe 0xbffffffffc0001ff

def z584 : W := mkw 0x0410804204080080 0x2010420108102002 0x0000c003000c00c0 0x000003000c003003

def z585 : W := mkw 0x0000000002010800 0x0000000000080420 0x00000000ce038c01 0x6000000003380e30

def z586 : W := mkw 0x0040050000402400 0x0001001400010090 0x00000f0000007c02 0x2000003c000001f0

def z587 : W := mkw 0x44bfc00054bc0004 0x9112ff000152f000 0x01ffc00031fc001d 0xc007ff0000c7f000

def z588 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c70f1f31c07fca 0x24071c3c7cc701ff

def z589 : W := mkw 0xf9a76894b9965105 0x97e69da252e65944 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z590 : W := mkw 0xabc37f0d10d43560 0x0aaf0dfc344350d5 0xffc7ff1f31fc7fff 0xffff1ffc7cc7f1ff

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c003003c03c0 0x840003000c00f00f

def z592 : W := mkw 0x06d2d74b06cd2ce0 0x201b4b5d2c1b34b3 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z593 : W := mkw 0xeff6ffff0002d303 0x8fbfdbfffc000b4c 0xffffffff0003f33e 0xbffffffffc000fcc

def z594 : W := mkw 0xab403f0000402400 0x0aad00fc00010090 0xffc03f0031c07c3f 0x7bff00fc00c701f0

def z595 : W := mkw 0xe9e76d9d10d43562 0x8fa79db6744350d5 0xf1c7cf1f31fc7fdf 0xf7c71f3c7cc7f1ff

def z596 : W := mkw 0xfffefffbe022c203 0x9ffffbffef808b08 0xffffffffc003803e 0x9fffffffff000e00

def z597 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f0cfc30307308 0x97c0fc33f0c0c1cc

def z598 : W := mkw 0x40a6409900000002 0x8502990264000000 0x0007001c00000000 0x00001c0070000000

def z599 : W := mkw 0xfff7ffdbb9940006 0x9fffdfff6ee65000 0xffffffff31c0003e 0x9ffffffffcc70000

def z600 : W := mkw 0x0001000410101100 0x0000040010404044 0x0007001c00300300 0x84001c007000c00c

def z601 : W := mkw 0x200028b00002c201 0x048000a2c0000b08 0x000030e000038000 0x000000c380000e00

def z602 : W := mkw 0x0200124202010880 0x2008004908080422 0x0000030300000cc0 0x0000000c0c000033

def z603 : W := mkw 0x0009002450309300 0x000024009140c24c 0x003f3cfcf033f33b 0xa400fcf3f3c0cfcc

def z604 : W := mkw 0xf9e76d99b9940006 0x9fe79db666e65000 0xf1c70c1c31c00008 0x13c71c3070c70000

def z605 : W := mkw 0xbb403f00a9000000 0x0aed00fc02a40000 0xffc03f00ffc0003f 0x5bff00fc03ff0000

def z606 : W := mkw 0x0200126202018a80 0x200800498808062a 0x000030e000038000 0x000000c380000e00

def z607 : W := mkw 0xaf50bf4200000000 0x0abd42fd08000000 0xfff8ffe30000003e 0x9fffe3ff8c000000

def z608 : W := mkw 0x30012804b0125100 0x00c004a012c04944 0xf0073c1cf033f33b 0xb7c01cf073c0cfcc

def z609 : W := mkw 0x0418806244288280 0x201062018910a20a 0x0038f0e3c03f83f3 0xa400e3c38f00fe0f

def z610 : W := mkw 0x00c2450d00403560 0x00030914340100d5 0x01c7cf1f00007fde 0xa4071f3c7c0001ff

def z611 : W := mkw 0x54bfc000f4bc0004 0x9152ff0003d2f000 0xf03fc000f03c0039 0x93c0ff0003c0f000

def z612 : W := mkw 0x32403f00a2436c00 0x48c900fc02890db0 0xf0003f00f003fc3b 0x33c000fc03c00ff0

def z613 : W := mkw 0x0658976f4669bfe0 0x2019625dbd19a6ff 0x0e38ffffce3ffff7 0xec38e3ffff38ffff

def z614 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e3830e0ce3f8fe1 0x6838e0c38338fe3f

def z615 : W := mkw 0xab403fdb00000002 0x0ead00ff6c000000 0xffc03fff0000003e 0x1fff00fffc000000

def z616 : W := mkw 0x0083400010940000 0x00020d0000425000 0x0007c000003c0000 0x80001f000000f000

def z617 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x003830e0f033f333 0xa400e0c383c0cfcc

def z618 : W := mkw 0x8fd2d74b06090882 0xaa3f4b5d2c182422 0x0fc0c3030e0c0cc4 0x483f030c0c383033

def z619 : W := mkw 0x22403f620243ee80 0x688900fd88090fba 0x00003fe30003ffc2 0x240000ff8c000fff

def z620 : W := mkw 0xb9402d00ab436c00 0x4ae500b402ad0db0 0xf1c00c00ffc3fc09 0x73c7003003ff0ff0

def z621 : W := mkw 0x2618baf6462bdb81 0x249862ebd918af6e 0x0e38ffffce3ffff7 0xec38e3ffff38ffff

def z622 : W := mkw 0x0610924206090880 0x2018424908182422 0x0e0000000e000000 0x0838000000380000

def z623 : W := mkw 0xa9402d0000000000 0x0aa500b400000000 0xf1c00c0000000008 0x13c7003000000000

def z624 : W := mkw 0x763dbaf6f032d301 0x15d8f6ebdbc0cb4c 0xfe3ffffff033f33f 0xbff8ffffffc0cfcc

def z625 : W := mkw 0xfbe67f99ab436c02 0xcfef99fe66ad0db0 0xffc73f1cffc3fc3f 0x7bff1cfc73ff0ff0

def z626 : W := mkw 0x402d00b450309301 0x1500b402d140c24c 0x003f0cfc3030731b 0xa400fc33f0c0c1cc

def z627 : W := mkw 0xcfbed26246298a80 0xa33efb498918a62a 0xfffff3e3ce3f8fff 0xffffffcf8f38fe3f

def z628 : W := mkw 0x0083400d10d43560 0x00020d00344350d5 0x0007c01f31fc7fc1 0xe4001f007cc7f1ff

def z629 : W := mkw 0xfb6d3f00fb736c00 0x5bedb4fc03edcdb0 0xffff3f00fff3fc3f 0xfbfffcfc03ffcff0

def z630 : W := mkw 0xfff7ffdfbbd77d62 0xcfffdfff7eef5df5 0xffffffffffffffff 0xffffffffffffffff

def z631 : W := mkw 0xfdffed00fdfe6404 0xdbf7ffb403f7f990 0xffffcc00fffc703d 0xdbffff3003fff1c0

def z632 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x0e003f00ce03fc37 0x683800fc03380ff0

def z633 : W := mkw 0xefffffff50309303 0x9fbffffffd40c24c 0xffffffff0030033e 0x9ffffffffc00c00c

def z634 : W := mkw 0xdfffd74bfdbc0006 0x9b7fff5d2ff6f000 0xffffc303fffc003d 0xdbffff0c0ffff000

def z635 : W := mkw 0x70af68b4f0b6d301 0x15c2bda2d3c2db4c 0xf1fffcfcf1fff33f 0xf7c7fff3f3c7ffcc

def z636 : W := mkw 0x50ef450df0f43560 0x1143bd1437c3d0d5 0xf1ffcf1ff1fc7fff 0xf7c7ff3c7fc7f1ff

def z637 : W := mkw 0x00c2450d00c43560 0x00030914340310d5 0x01c0cf1f01cc7fc6 0x6407033c7c0731ff

def z638 : W := mkw 0x0618926244288280 0x201862498910a20a 0x0e38f3e3003c03f6 0x8c38e3cf8c00f00f

def z639 : W := mkw 0x8f92d2420f8d0884 0xa23e4b49083e3422 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z640 : W := mkw 0xeffeffdb44280002 0x8fbffbff6d10a000 0xffffffffce3c003f 0xdfffffffff38f000

def z641 : W := mkw 0x8b40170000000000 0x0a2d005c00000000 0x0fc0030000000004 0x083f000c00000000

def z642 : W := mkw 0x10cb450dfdfc3564 0x10432d1437f7f0d5 0x01c7cf1ffffc7fdf 0xe4071f3c7ffff1ff

def z643 : W := mkw 0x0040050000000000 0x0001001400000000 0x01c00f000000001e 0x0007003c00000000

def z644 : W := mkw 0x8dd2c5090dcc2464 0x82374b1424373091 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z645 : W := mkw 0x8f5897624f69ae80 0x6a3d625d893da6ba 0x0ff8f3e3cfff8ff7 0xec3fe3cf8f3ffe3f

def z646 : W := mkw 0x10c3450dbbd77d60 0x40430d1436ef5df5 0x01c7cf1fffffffdf 0xe4071f3c7fffffff

def z647 : W := mkw 0x763cbaf2e62bca81 0x35d8f2ebcb98af2a 0xfe38f3e3ce3f8ff7 0xfff8e3cf8f38fe3f

def z648 : W := mkw 0x8fd2d74b0d8c0006 0x8a3f4b5d2c363000 0x0fc0c3030fcc0004 0x483f030c0c3f3000

def z649 : W := mkw 0xffbffa00ffbf4804 0xdbfeffe803fefd20 0xfffff000ffff803d 0xdbffffc003fffe00

def z650 : W := mkw 0xbf50bf42af4b6c80 0x6afd42fd0abd2db2 0xffc0ff03ffcffcff 0x7bff03fc0fff3ff3

def z651 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cc1c31fc701d 0xc0071f3070c7f1c0

def z652 : W := mkw 0xab403f0002010800 0x0aad00fc00080420 0xffc03f00ce038c3f 0x7bff00fc03380e30

def z653 : W := mkw 0xd9e7450db9d43564 0x93679d1436e750d5 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z654 : W := mkw 0x0200120002010800 0x0008004800080420 0x0e0003000e000c04 0x4838000c00380030

def z655 : W := mkw 0x743da8f6f43ad381 0x35d0f6a3dbd0eb4e 0xf03ffcfff03ff3fb 0xb7c0fff3ffc0ffcf

def z656 : W := mkw 0x0040050d00403560 0x00010014340100d5 0x01c00f1f31c07fdf 0x6407003c7cc701ff

def z657 : W := mkw 0x74bfe8fff032d303 0x95d2ffa3ffc0cb4c 0xf03ffcfff033f33b 0xb7c0fff3ffc0cfcc

def z658 : W := mkw 0xef34bad200000002 0x8fbcd2eb48000000 0xfe38f3e300000036 0x9ff8e3cf8c000000

def z659 : W := mkw 0xbb403f00a0024000 0x0aed00fc02800900 0xffc03f00f003f03f 0x3bff00fc03c00fc0

def z660 : W := mkw 0x0001000010940000 0x0000040000425000 0x0000000031fc0001 0x4000000000c7f000

def z661 : W := mkw 0xcd34800000000000 0x8334d20000000000 0xfe38000000000020 0x1bf8e00000000000

def z662 : W := mkw 0x502d0020f0308200 0x1140b40083c0c208 0xf03f30e0f033833b 0xb7c0fcc383c0ce0c

def z663 : W := mkw 0x44b7c0df10941162 0x8512df037c425045 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z664 : W := mkw 0xff3cbaf2e022c203 0x9ffcf2ebcb808b08 0xfe3830e0c0038020 0x1bf8e0c383000e00

def z665 : W := mkw 0x44ffc50d54fc3564 0x9113ff143553f0d5 0x01ffcf1f31fc7fdf 0xe407ff3c7cc7f1ff

def z666 : W := mkw 0x702d28b0f032c201 0x15c0b4a2c3c0cb08 0xf03f30e0f0338039 0x93c0fcc383c0ce00

def z667 : W := mkw 0x44bfc06254bc8284 0xb112ff018952f20a 0x003fc0e3003c03c0 0x8400ff038c00f00f

def z668 : W := mkw 0x702c28b0e022c201 0x15c0b0a2c3808b08 0xf03830e0c0338333 0xb7c0e0c38300ce0c

def z669 : W := mkw 0x22c27fdb00000002 0x0c8b09ff6c000000 0x01c7ffff0000001e 0x84071ffffc000000

def z670 : W := mkw 0xdd3d8000fdbc0004 0x9374f60003f6f000 0xfe380000fffc0021 0x5bf8e00003fff000

def z671 : W := mkw 0x00cb452d50f4b760 0x00032d14b543d2dd 0x01fffffff1ffffff 0xe407ffffffc7ffff

def z672 : W := mkw 0x000000000d8c0004 0x0000000000363000 0x000000000fcc0000 0x40000000003f3000

def z673 : W := mkw 0xcdbfc00054bc0004 0x9336ff000152f000 0xffffc000003c003c 0x9bffff000000f000

def z674 : W := mkw 0xe924289000000002 0x8fa490a240000000 0xf000000000000000 0x13c0000000000000

def z675 : W := mkw 0xfffeffdbed280006 0x9ffffbff6fb4a000 0xffffffffce00003e 0x9fffffffff380000

def z676 : W := mkw 0x463d92f656399b81 0x3518f64bd958e66e 0x0e3ff3ffce3f8ff7 0xec38ffcfff38fe3f

def z677 : W := mkw 0x8bc3570d1bd53d60 0x4a2f0d5c346f54f5 0x0fc7cf1f3ffc7fdf 0xec3f1f3c7cfff1ff

def z678 : W := mkw 0x14198000fdbc0004 0x1050660003f6f000 0x0e38c000fffc0035 0xc838e30003fff000

def z679 : W := mkw 0x0208122042218a00 0x0008204881088628 0x0e3833e0ce338f37 0xec38e0cf8338ce3c

def z680 : W := mkw 0x000000b400009301 0x04000002d000024c 0x000000fc00000300 0x04000003f000000c

def z681 : W := mkw 0x89c2450900000002 0x8a27091424000000 0x01c0000000000000 0x0007000000000000

def z682 : W := mkw 0xeff7ffdf10d43562 0x8fbfdfff7c4350d5 0xffffffff31c0703e 0x9ffffffffcc701c0

def z683 : W := mkw 0x50af4000f0b40000 0x1142bd0003c2d000 0xf1ffc000f1fc003d 0xd3c7ff0003c7f000

def z684 : W := mkw 0x10010004bbd77d60 0x4040040012ef5df5 0x00000000ffffffc1 0x6000000003ffffff

def z685 : W := mkw 0x40a7400010940004 0x91029d0000425000 0x0007000000000000 0x00001c0000000000

def z686 : W := mkw 0xbb413f04bbd77d60 0x4aed04fc12ef5df5 0xffc03f00ffffffff 0x7bff00fc03ffffff

def z687 : W := mkw 0x108b4000fdbc0004 0x10422d0003f6f000 0x01c7c000fffc001d 0xc0071f0003fff000

def z688 : W := mkw 0x04dbc50d54fc3560 0x00136f143553f0d5 0x0fffcf1ffffc7fff 0xec3fff3c7ffff1ff

def z689 : W := mkw 0x0418806244288280 0x201062018910a20a 0x0038c3e3003c0fd7 0xe400e30f8c00f03f

def z690 : W := mkw 0x0000000006090880 0x2000000000182422 0x000000000e0c0cc0 0x4000000000383033

def z691 : W := mkw 0x30402d00a0426400 0x00c100b402810990 0xf1c03f00f1c3fc3f 0x73c700fc03c70ff0

def z692 : W := mkw 0x702c28b0e022c201 0x15c0b0a2c3808b08 0xf0383ce0f003f03b 0x33c0e0f383c00fc0

def z693 : W := mkw 0x54bfc000fdbc0004 0x9152ff0003f6f000 0x003fc000fffc0001 0xc000ff0003fff000

def z694 : W := mkw 0x32403f00ab436c00 0x48c900fc02ad0db0 0x00003f00ffc3fc03 0x600000fc03ff0ff0

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000003c0fc1 0x600000000000f03f

def z696 : W := mkw 0x76fffffff6ffffe1 0x35dbffffffdbffff 0xffffffffffffffff 0xffffffffffffffff

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c303000c0cc4 0x4000030c0c003033

def z698 : W := mkw 0xefb6fad200000002 0x8fbedbeb48000000 0xfffff0e00000003c 0x9bffffc380000000

def z699 : W := mkw 0xff7dbff6ff7bff81 0x7ffdf6ffdbfdeffe 0xffffffffffffffff 0xffffffffffffffff

def z700 : W := mkw 0x8982400009840004 0x8226090000261000 0x01c0000001c00000 0x0007000000070000

def z701 : W := mkw 0xddffc509fdbc0004 0x9377ff1427f6f000 0xffffcf1ffffc003f 0xdfffff3c7ffff000

def z702 : W := mkw 0x0200120000000000 0x0008004800000000 0x0e00330000000036 0x083800cc00000000

def z703 : W := mkw 0x00c3450010d42400 0x00030d1400435090 0x01c7cf0031fc7c1f 0xe0071f3c00c7f1f0

def z704 : W := mkw 0xffffff00fdbc0004 0x9bfffffc03f6f000 0xffffff00fffc003f 0xdbfffffc03fff000

def z705 : W := mkw 0x16199262ffbd8a84 0x305866498bfef62a 0x0e38f3e3ffff8ff7 0xec38e3cf8ffffe3f

def z706 : W := mkw 0x0082400900840060 0x0002090024021001 0x0000c003000c00c0 0x000003000c003003

def z707 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff00000c3f 0xfffffffffc000030

def z708 : W := mkw 0x22c37f0d12d77d60 0x488b0dfc344b5df5 0x0007ff1f003fffc2 0xa4001ffc7c00ffff

def z709 : W := mkw 0x9d92c000ad8c0004 0x82764b0002b63000 0xffc0c000cfcc0024 0x5bff0300033f3000

def z710 : W := mkw 0xeff6ffdb00402402 0x8fbfdbff6c010090 0xffffffff31c0703e 0x9ffffffffcc701c0

def z711 : W := mkw 0xddbfc004fdbe5105 0x9376ff0013f6f944 0xffffc000fffc703d 0xdbffff0003fff1c0

def z712 : W := mkw 0x99000000a9024000 0x0264000002a40900 0xffc00000ffc3f03d 0x7bff000003ff0fc0

def z713 : W := mkw 0x6024289000024000 0x058090a240000900 0xf03f3cfc0003f03a 0xb7c0fcf3f0000fc0

def z714 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00000000f003f000 0x0000000003c00fc0

def z715 : W := mkw 0xd92d00b4f9309301 0x1764b402d3e4c24c 0xffff00fcfff0033d 0xdffffc03f3ffc00c

def z716 : W := mkw 0x8900000009000000 0x0224000000240000 0xffc000000fc0003c 0x5bff0000003f0000

def z717 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0ff8f3e3ffff8fff 0xec3fe3cf8ffffe3f

def z718 : W := mkw 0x22403fdf02437d62 0x4c8900ff7c090df5 0x00003fff0003ffc2 0x240000fffc000fff

def z719 : W := mkw 0x22403f4b02436c02 0x488900fd2c090db0 0x00003f030003fc02 0x200000fc0c000ff0

def z720 : W := mkw 0xe924289000000000 0x07a490a240000000 0xffff3cfc0000003e 0x9ffffcf3f0000000

def z721 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03f3cfc00000028 0x13c0fcf3f0000000

def z722 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03c00ffc3fc29 0x7bff00f003ff0ff0

def z723 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03f30fc00000020 0x97c0fcc3f0000000

def z724 : W := mkw 0xeff6ffdb02010882 0xafbfdbff6c080422 0xffffffff00000cfe 0x9ffffffffc000033

def z725 : W := mkw 0x66ffff0056ff6c04 0xd99bfffc015bfdb0 0x003fff00003ffc02 0xa000fffc0000fff0

def z726 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xfffff3ff00000024 0x9fffffcffc000000

def z727 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc003fffc03fd 0xdfffff000ffff00f

def z728 : W := mkw 0xd9240000a9000004 0x9364900002a40000 0xffc00000ffc0003d 0x5bff000003ff0000

def z729 : W := mkw 0xef35bad610d43562 0x8fbcd6eb584350d5 0xfe3830e031fc7fe1 0x7bf8e0c380c7f1ff

def z730 : W := mkw 0x10090024fdbc9305 0x1040240093f6f24c 0x00000000fffc0301 0x4000000003fff00c

def z731 : W := mkw 0x22403f9002436c00 0x4c8900fe40090db0 0x00003ffc0003fc02 0x240000fff0000ff0

def z732 : W := mkw 0x22403f620243ee80 0x688900fd88090fba 0x00003fe00003fc02 0x200000ff80000ff0

def z733 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38ffe3fe3fffff 0xec38e3ff8ff8ffff

def z734 : W := mkw 0x6634bad200000000 0x0598d2eb48000000 0xfe3f3cfc0000003a 0x9ff8fcf3f0000000

def z735 : W := mkw 0xcfb6d2db00000002 0x873edb4b6c000000 0xfffff3ff0000003e 0x9fffffcffc000000

def z736 : W := mkw 0x9b401700ab412c00 0x026d005c02ad04b0 0xffc03f00ffc3fc3f 0x7bff00fc03ff0ff0

def z737 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc00000cfc00024 0x5bff0000033f0000

def z738 : W := mkw 0x99090024f932d301 0x1264240093e4cb4c 0xffc00000fff3f33d 0x7bff000003ffcfcc

def z739 : W := mkw 0xab403f0002412c00 0x0aad00fc000904b0 0xffc03f00ffc3fc3f 0x7bff00fc03ff0ff0

def z740 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e3fffffce3f8fff 0xec38ffffff38fe3f

def z741 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03fffff003c0fff 0xf7c0fffffc00f03f

def z742 : W := mkw 0xbb837a0dbb975960 0x4aee0de836ee5d65 0xfe07f01fce3f83e0 0x9ff81fc07f38fe0f

def z743 : W := mkw 0x10090024f0309301 0x1040240093c0c24c 0x00000000f0300301 0x0000000003c0c00c

def z744 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x00003f030003ffc2 0x240000fc0c000fff

def z745 : W := mkw 0x10090024ffffff05 0x5040240093fffffc 0x00000000ffffff01 0x6000000003fffffc

def z746 : W := mkw 0xeb643f900b412c00 0x4fad90fe402d04b0 0xffff3ffc0fc00c3e 0xdffffcfff03f0030

def z747 : W := mkw 0xddbfc06ffdbc93e4 0xb376ff01bff6f24f 0xffffc0fffffc03fd 0xdfffff03fffff00f

def z748 : W := mkw 0xdd3d8000fdbc0004 0x9374f60003f6f000 0xfff80000fffc003d 0x5bffe00003fff000

def z749 : W := mkw 0xad92e8b40d8ed305 0x86b64ba2d0363b4c 0x0fc0fcfc0fcff306 0x6c3f03f3f03f3fcc

def z750 : W := mkw 0x22403f0002412c00 0x488900fc000904b0 0x00003f0000000c02 0x000000fc00000030

def z751 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffcc1cfffc003f 0xdfffff3073fff000

def z752 : W := mkw 0xddbfc094fdbc1105 0x9776ff0253f6f044 0xffffc01cfffc003d 0xdbffff0073fff000

def z753 : W := mkw 0x00c2450900402400 0x0003091424010090 0x01c7cf1f31fc7fdf 0xe4071f3c7cc7f1ff

def z754 : W := mkw 0xeb643fdb00000002 0x0fad90ff6c000000 0xffff3fff0000003e 0x9ffffcfffc000000

def z755 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f3e3ce3f8fe5 0x6838e3cf8f38fe3f

def z756 : W := mkw 0x8fd2d74b0fcd2c06 0xca3f4b5d2c3f34b0 0x0fc0c3030fcc0c04 0x483f030c0c3f3030

def z757 : W := mkw 0x62643f9000000000 0x0d8990fe40000000 0xf03f3ffc0000003a 0x97c0fcfff0000000

def z758 : W := mkw 0xedb6e8db00000002 0x8fb6dba36c000000 0xf03fc0ff00000000 0x97c0ff03fc000000

def z759 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc000cffc0024 0xdbffff00033ff000

def z760 : W := mkw 0x32493fdbfdbc0006 0x1cc924ff6ff6f000 0x00003ffffffc0003 0x440000fffffff000

def z761 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc73f1cffc3fc3f 0xffff1cfc73ff0ff0

def z762 : W := mkw 0x22403f9402437d01 0x4c8900fe50090df4 0x00003f1c0003fc02 0x200000fc70000ff0

def z763 : W := mkw 0x602c28b44022d301 0x0580b0a2d1008b4c 0xf03f3cfcc033f33b 0xb7c0fcf3f300cfcc

def z764 : W := mkw 0x4024009000000000 0x0500900240000000 0xf03f00fc00000038 0x97c0fc03f0000000

def z765 : W := mkw 0xcff6d74b00000000 0x833fdb5d2c000000 0xffffffff0000003e 0x9ffffffffc000000

def z766 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x0000000030307300 0x0000000000c0c1cc

def z767 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x0000c303f03fffd7 0xe400030c0fc0ffff

def z768 : W := mkw 0xcdf6c5db00000002 0x8737db176c000000 0xffffcfff0000003e 0x9fffff3ffc000000

def z769 : W := mkw 0x22403ffb0243ee82 0x6c8900ffec090fba 0x00003fff0003ffc2 0x240000fffc000fff

def z770 : W := mkw 0xcdb6c0000d8c0004 0x8336db0000363000 0xffc7c0000fcc000c 0x5bff1f00003f3000

def z771 : W := mkw 0x44bfc02454bc9305 0x9112ff009152f24c 0x003fc000003c0300 0x8000ff000000f00c

def z772 : W := mkw 0xd9a74000b9940004 0x93669d0002e65000 0xffc70000ffc00028 0x1bff1c0003ff0000

def z773 : W := mkw 0xbb403f09ab436c00 0x4aed00fc26ad0db0 0xffc03f1fffc3fc3f 0x7fff00fc7fff0ff0

def z774 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc00c00ffc0703f 0x7bff003003ff01c0

def z775 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00003000f033f333 0x200000c003c0cfcc

def z776 : W := mkw 0x9b491724fb73ff01 0x5a6d245c93edcffc 0x0fc00300fff3ff05 0x683f000c03ffcffc

def z777 : W := mkw 0xcb6d17b45b71bf01 0x5f2db45ed16dc6fc 0x0fff03fc0ff00f04 0xcc3ffc0ff03fc03c

def z778 : W := mkw 0xddbec000edac0004 0x9376fb0003b6b000 0xfff8c000ffcc003d 0x5bffe30003ff3000

def z779 : W := mkw 0x10090024f0b6d301 0x1040240093c2db4c 0x00000000f1fff301 0x6000000003c7ffcc

def z780 : W := mkw 0xd92d0000fdbc0004 0x1364b40003f6f000 0xffff0000fffc003d 0xdbfffc0003fff000

def z781 : W := mkw 0xd9240000a9000000 0x0364900002a40000 0xffff0000ffc0003d 0xdbfffc0003ff0000

def z782 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03ffffff033f33f 0xb7c0ffffffc0cfcc

def z783 : W := mkw 0x10090024fbf7ff61 0x5040240093efdffd 0x00000000ffffffc1 0x6000000003ffffff

def z784 : W := mkw 0xddbfc00dfdbc1164 0x9376ff0037f6f045 0xffffc31ffffc0fff 0xffffff0c7ffff03f

def z785 : W := mkw 0xbb403f42ab436c00 0x4aed00fd0aad0db0 0xffc03fe3ffc3fc3f 0x7fff00ff8fff0ff0

def z786 : W := mkw 0x9fdbd76ff032d303 0x9a7f6f5dbfc0cb4c 0x0fc0c303f033f305 0x283f030c0fc0cfcc

def z787 : W := mkw 0xeff6ffdb02412c02 0xcfbfdbff6c0904b0 0xffffffff00000c3e 0x9ffffffffc000030

def z788 : W := mkw 0x99400500ab436c00 0x4265001402ad0db0 0xffc00f00ffc3fc3f 0x7bff003c03ff0ff0

def z789 : W := mkw 0xcdb6c0db00000002 0x8736db036c000000 0xfe3fc0ff00000020 0x9ff8ff03fc000000

def z790 : W := mkw 0x99000000ad8c0004 0x0264000002b63000 0xffc00000ffcc003d 0x5bff000003ff3000

def z791 : W := mkw 0x8fd2d74b0bc52c62 0xca3f4b5d2c2f14b1 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z792 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc0ff00fffffc3f 0xfbff03fc03fffff0

def z793 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xfffff0e0fffc003f 0xdfffffc383fff000

def z794 : W := mkw 0xeff6ffdb04080082 0xafbfdbff6c102002 0xffffffff000c00fe 0x9ffffffffc003003

def z795 : W := mkw 0xb9402d00a9426400 0x4ae500b402a50990 0xffc03c00ffc3f03f 0x7bff00f003ff0fc0

def z796 : W := mkw 0x8fd2d74b02412c02 0xca3f4b5d2c0904b0 0x0fc0c30300000c04 0x083f030c0c000030

def z797 : W := mkw 0x10090024fb33db01 0x5040240093eccf6c 0x00000000fe33f301 0x2000000003f8cfcc

def z798 : W := mkw 0xef74bfd200000000 0x0fbdd2ff48000000 0xffffffff0000003e 0x9ffffffffc000000

def z799 : W := mkw 0x7635bad6b61b5981 0x35d8d6eb5ad86d66 0xfe07cf1f3e0c7ccc 0x5bf81f3c7cf831f3

def z800 : W := mkw 0xef34bad200000002 0x8fbcd2eb48000000 0xfe3f3cfc00000028 0x1bf8fcf3f0000000

def z801 : W := mkw 0x9d93c000bd9c0004 0x82764f0002f67000 0xffc7c000fffc003d 0xdbff1f0003fff000

def z802 : W := mkw 0xdba75262bb958a84 0xb36e9d498aee562a 0xf1c733e331c38fca 0x37c71ccf8cc70e3f

def z803 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x0000330000038c00 0x000000cc00000e30

def z804 : W := mkw 0x9d108000ad080004 0x8274420002b42000 0xffc00000ffc0003d 0x5bff000003ff0000

def z805 : W := mkw 0x9d108000a9000000 0x0274420002a40000 0xfff8c000ffc0003d 0xdbffe30003ff0000

def z806 : W := mkw 0xdd3d8000fd380004 0x9374f60003f4e000 0xffff0000fff0003d 0xdbfffc0003ffc000

def z807 : W := mkw 0x32493f24f273ff01 0x58c924fc93c9cffc 0x00003f00f033ff03 0x200000fc03c0cffc

def z808 : W := mkw 0x10090024fffdbfe4 0x3040240093fff6ff 0x00000000ffffffc1 0x6000000003ffffff

def z809 : W := mkw 0xcdb7c0001d9c0004 0x8336df0000767000 0xffffc0003ffc003d 0xdbffff0000fff000

def z810 : W := mkw 0xed34a89000000000 0x87b4d2a240000000 0xfe3f3cfc0000003a 0x9ff8fcf3f0000000

def z811 : W := mkw 0xff3cbaf2ef2bca81 0x7ffcf2ebcbbcaf2a 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z812 : W := mkw 0xddbfc00dfdbc1164 0x9376ff0037f6f045 0xffffcc1ffffc73ff 0xffffff307ffff1cf

def z813 : W := mkw 0x54b6c0dbab436c02 0xc552db036ead0db0 0x003fc0ffffc3fc01 0xe400ff03ffff0ff0

def z814 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00000000c0338300 0x000000000300ce0c

def z815 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x00003f00c003fc33 0x200000fc03000ff0

def z816 : W := mkw 0xddbfc020fdbc8204 0x9376ff0083f6f208 0xffffc000ffff833d 0xfbffff0003fffe0c

def z817 : W := mkw 0x22403fff0241bfe2 0x2c8900fffc0906ff 0x00003fff0003ffc2 0x240000fffc000fff

def z818 : W := mkw 0xeff6ffdb00c42462 0x8fbfdbff6c031091 0xffffffff01c0003e 0x9ffffffffc070000

def z819 : W := mkw 0x702c28b0e022c201 0x15c0b0a2c3808b08 0xf03f3cfcf003f03b 0xb7c0fcf3f3c00fc0

def z820 : W := mkw 0xddb7c000bd9c0004 0x9376df0002f67000 0xffffc0003fcc003c 0xdbffff0000ff3000

def z821 : W := mkw 0x9d198000fdbc0004 0x1274660003f6f000 0xfff8c000fffc003d 0xdbffe30003fff000

def z822 : W := mkw 0xeff6ffdb00426402 0xcfbfdbff6c010990 0xffffffff0000703e 0x9ffffffffc0001c0

def z823 : W := mkw 0x22403fd202436c02 0x4c8900ff48090db0 0x00003fe00003fc02 0x200000ff80000ff0

def z824 : W := mkw 0xeff6ffdb00402402 0x8fbfdbff6c010090 0xffffffff31fc7fff 0xfffffffffcc7f1ff

def z825 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f3e3ce3f8fe2 0xac38e3cf8f38fe3f

def z826 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc303fffc0cfd 0xdbffff0c0ffff033

def z827 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf003f03b 0x33c0fcf3f3c00fc0

def z828 : W := mkw 0x99010000b9100000 0x0264040002e44000 0xffc70000fff0003d 0xdbff1c0003ffc000

def z829 : W := mkw 0x60642d9000402400 0x058190b640010090 0xf1ff3ffc31c07c3f 0xf7c7fcfff0c701f0

def z830 : W := mkw 0xeff6ff9000000000 0x8fbfdbfe40000000 0xfffffffc0000003e 0x9ffffffff0000000

def z831 : W := mkw 0xd9a74000b9940004 0x93669d0002e65000 0xffc700003fc0000c 0x5bff1c0000ff0000

def z832 : W := mkw 0xeff6ffdb09000002 0x8fbfdbff6c240000 0xffffffff0fc0003e 0xdffffffffc3f0000

def z833 : W := mkw 0x10090024fdfef765 0x1040240093f7fbdd 0x00000000ffffffc1 0x6000000003ffffff

def z834 : W := mkw 0x702d28b4f932d301 0x15c0b4a2d3e4cb4c 0xf03f3cfcfff3f33b 0xf7c0fcf3f3ffcfcc

def z835 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffff3cfc0000003a 0x9ffffcf3f0000000

def z836 : W := mkw 0xddbec000ed280004 0x9376fb0003b4a000 0xffffc000ffc0003d 0xdbffff0003ff0000

def z837 : W := mkw 0x9b401700ab436c00 0x4a6d005c02ad0db0 0xffc00300ffc3fc3d 0x7bff000c03ff0ff0

def z838 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf03ffffb 0xf7c0fcf3f3c0ffff

def z839 : W := mkw 0xddbfc024fdbc9304 0x9376ff0093f6f24c 0xfffffcfcfffff33f 0xfffffff3f3ffffcc

def z840 : W := mkw 0x9d9ac000edac0004 0x82766b0003b6b000 0xfff8c000fffc003d 0xdbffe30003fff000

def z841 : W := mkw 0xe9a6689000000000 0x87a699a240000000 0xf1ff3cfc0000003a 0x97c7fcf3f0000000

def z842 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01ffffff31fc7fff 0xe407fffffcc7f1ff

def z843 : W := mkw 0x22403f0d02437d60 0x488900fc34090df5 0x00003f1c0003fc02 0x200000fc70000ff0

def z844 : W := mkw 0x10090024fd3ad305 0x1040240093f4eb4c 0x00000000fe33f301 0x2000000003f8cfcc

def z845 : W := mkw 0x702428b4a002d301 0x05c090a2d2800b4c 0xf03f3cfcf003f33b 0xb7c0fcf3f3c00fcc

def z846 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf003f32a 0x37c0fcf3f3c00fcc

def z847 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x0fc7cf1ffffc7fff 0xec3f1f3c7ffff1ff

def z848 : W := mkw 0xbb403f99ab436c02 0x4eed00fe66ad0db0 0xffc03f1cffc3fc3f 0x7bff00fc73ff0ff0

def z849 : W := mkw 0x9d9bc000fdbc0004 0x92766f0003f6f000 0xffc0c000fffc003d 0x5bff030003fff000

def z850 : W := mkw 0xff3cbaf2ef2bca82 0xeffcf2ebcbbcaf2a 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z851 : W := mkw 0xeff6ffdb0bc52c62 0xcfbfdbff6c2f14b1 0xffffffff0fcc0cfe 0xdffffffffc3f3033

def z852 : W := mkw 0xe9ee6db946298a82 0xafa7b9b6e518a62a 0xf1c70c1cce3f8fc9 0x73c71c307338fe3f

def z853 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc00000ffc00028 0x1bff000003ff0000

def z854 : W := mkw 0xbb403fd2ab436c02 0x4eed00ff4aad0db0 0xffc03fe0ffc3fc3f 0x7bff00ff83ff0ff0

def z855 : W := mkw 0x99824000a9000000 0x0266090002a40000 0xffc7c000ffc0003d 0xdbff1f0003ff0000

def z856 : W := mkw 0xddbfc099fdbc0006 0x9776ff0267f6f000 0xffffc01cfffc003d 0xdbffff0073fff000

def z857 : W := mkw 0x626d3fb45273ff01 0x5d89b4fed149cffc 0x003f3ffc0033ff02 0xa400fcfff000cffc

def z858 : W := mkw 0xddbfc062fdbc8284 0xb376ff018bf6f20a 0xffffc0e0fffc003d 0xdbffff0383fff000

def z859 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc0003ffc000c 0xdbffff0000fff000

def z860 : W := mkw 0xddbfc000f9300000 0x9376ff0003e4c000 0xffffc000fff0003d 0xdbffff0003ffc000

def z861 : W := mkw 0xddbfc004fdbc1104 0x9376ff0013f6f044 0xffffc000fffc733d 0xfbffff0003fff1cc

def z862 : W := mkw 0x0083400410941100 0x00020d0010425044 0x01c7cf1f31fc7fdf 0xe4071f3c7cc7f1ff

def z863 : W := mkw 0xeff6ffdb0b412c02 0xcfbfdbff6c2d04b0 0xffffffffcfc38c3f 0xffffffffff3f0e30

def z864 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff31c0003f 0xdffffffffcc70000

def z865 : W := mkw 0x70ee6db9e0e6e661 0x15c3b9b6e7839b99 0xf1f8f3e3c1cf8ce4 0x53c7e3cf8f073e33

def z866 : W := mkw 0x99080000e9200000 0x0264200003a48000 0xfff80000fff0003d 0xdbffe00003ffc000

def z867 : W := mkw 0xeff6ffdb02010802 0x8fbfdbff6c080420 0xffffffff00038c3e 0xbffffffffc000e30

def z868 : W := mkw 0xddbfc0b4fdbed305 0x9776ff02d3f6fb4c 0xffffc0fcfffff33d 0xffffff03f3ffffcc

def z869 : W := mkw 0x60642d9900000002 0x0d8190b664000000 0xf03f3cfc0000003a 0x97c0fcf3f0000000

def z870 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x00003f000003fc17 0x600000fc00000ff0

def z871 : W := mkw 0xddbec000ed280000 0x8376fb0003b4a000 0xffffc000fffc003d 0xdbffff0003fff000

def z872 : W := mkw 0xcff6d7db00000002 0x8f3fdb5f6c000000 0xffffc3ff0000003c 0x9fffff0ffc000000

def z873 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cf1f31fc7fcd 0x60071f3c7cc7f1ff

def z874 : W := mkw 0x66f6ffdb00000002 0x8d9bdbff6c000000 0xf03fffff0000003a 0x97c0fffffc000000

def z875 : W := mkw 0x22403fff0243ffe1 0x248900fffc090fff 0x00003fff0003ffc2 0x240000fffc000fff

def z876 : W := mkw 0x998b4000fdbc0004 0x12662d0003f6f000 0xffc7c000fffc003d 0xdbff1f0003fff000

def z877 : W := mkw 0x99080020e9208200 0x0264200083a48208 0xfff830e0fff3833f 0xffffe0c383ffce0c

def z878 : W := mkw 0xddbfc090fdbc0004 0x9776ff0243f6f000 0xffffc0fcfffc003d 0xdfffff03f3fff000

def z879 : W := mkw 0x99080000ed280004 0x1264200003b4a000 0xffc00000ffc0003d 0x5bff000003ff0000

def z880 : W := mkw 0xddb7c000b9940004 0x9376df0002e65000 0xffffc000ffc0003d 0xdbffff0003ff0000

def z881 : W := mkw 0xcdbfc0005dbc0004 0x9336ff000176f000 0xffffc0000ffc003c 0xdbffff00003ff000

def z882 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03f00fff3ff3f 0xffff00fc03ffcffc

def z883 : W := mkw 0x22403f4202436c00 0x488900fd08090db0 0x00003fe30003fc02 0x240000ff8c000ff0

def z884 : W := mkw 0xeff6ffdb048c0006 0x8fbfdbff6c123000 0xffffffff000c003e 0x9ffffffffc003000

def z885 : W := mkw 0xeff6ffdb02436c02 0xcfbfdbff6c090db0 0xffffffff31c3fc3f 0xfffffffffcc70ff0

def z886 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc300fffc0c3f 0xfbffff0c03fff030

def z887 : W := mkw 0x99834000b9940000 0x02660d0002e65000 0xffc70000ffc0003d 0x5bff1c0003ff0000

def z888 : W := mkw 0x06dbd76f56fdbfe0 0x201b6f5dbd5bf6ff 0x0fff3cfcffc3f028 0x083ffcf3f3ff0fc0

def z889 : W := mkw 0xddbfc0bdfdbc9365 0x9776ff02f7f6f24d 0xffffc0fffffc03fd 0xdfffff03fffff00f

def z890 : W := mkw 0xf9e76d9db9d67565 0x97e79db676e759d5 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z891 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cf1f31fc7fca 0xa4071f3c7cc7f1ff

def z892 : W := mkw 0xddb6c000ad8c0004 0x8376db0002b63000 0xffffc000ffcc003d 0xdbffff0003ff3000

def z893 : W := mkw 0xeff6ffdb00840002 0x8fbfdbff6c021000 0xffffffff01cc003e 0xdffffffffc073000

def z894 : W := mkw 0x22403f200243ee00 0x488900fc80090fb8 0x00003fe00003ff02 0x240000ff80000ffc

def z895 : W := mkw 0x32403f00a2436c00 0x48c900fc02890db0 0x00003f00f003fc03 0x200000fc03c00ff0

def z896 : W := mkw 0xddb6c0dba9000002 0x8776db036ea40000 0xffffc0ffffc0003d 0xdfffff03ffff0000

def z897 : W := mkw 0x10090024f233db01 0x1040240093c8cf6c 0x00000000fe33ff01 0x6000000003f8cffc

def z898 : W := mkw 0x16199266f63bdb81 0x305866499bd8ef6e 0x0e00c303fe3fffc5 0x6838030c0ff8ffff

def z899 : W := mkw 0xeff6ffdb00024002 0x8fbfdbff6c000900 0xffffffff0003f03e 0xbffffffffc000fc0

def z900 : W := mkw 0x602d28b45032d301 0x1580b4a2d140cb4c 0xf03f3cfc0033f33a 0xb7c0fcf3f000cfcc

def z901 : W := mkw 0x10090024f0f6f761 0x1040240093c3dbdd 0x00000000f1f3f301 0x2000000003c7cfcc

def z902 : W := mkw 0xddbfc0fffdbc9307 0x9776ff03fff6f24c 0xffffc0fffffc033d 0xdfffff03fffff00c

def z903 : W := mkw 0xedf6eddb00000002 0x8fb7dbb76c000000 0xf1ffcfff0000001e 0x97c7ff3ffc000000

def z904 : W := mkw 0x9d108000ad080000 0x0274420002b42000 0xffc0c000ffcc003d 0x5bff030003ff3000

def z905 : W := mkw 0xbd58ad62ed6ae680 0x6af562b58bb5ab9a 0xf1f8cce331fc73c8 0x97c7e3338cc7f1cf

def z906 : W := mkw 0x62243ad200000000 0x058890eb48000000 0xf03f3fff0000003a 0x97c0fcfffc000000

def z907 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffcc00fffc703f 0xfbffff3003fff1c0

def z908 : W := mkw 0x62e67fdb00000002 0x0d8b99ff6c000000 0xf1ffffff0000003e 0x97c7fffffc000000

def z909 : W := mkw 0x10490524f072f701 0x1041241493c1cbdc 0x01c00f00f1f3ff1f 0x6007003c03c7cffc

def z910 : W := mkw 0xddb7c000b9940000 0x8376df0002e65000 0xffffc000fffc003d 0xdbffff0003fff000

def z911 : W := mkw 0xdd7c850ded683564 0x9375f21437b5a0d5 0xfe380f1fce007fe2 0x3ff8e03c7f3801ff

def z912 : W := mkw 0x10090024f233db81 0x3040240093c8cf6e 0x00000000f033ffc1 0x2000000003c0cfff

def z913 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xfe3fffff00000022 0x9ff8fffffc000000

def z914 : W := mkw 0xddbfc024fdbed305 0x9376ff0093f6fb4c 0xffffcc1cfffff33f 0xffffff3073ffffcc

def z915 : W := mkw 0xcdb6c00009000000 0x8336db0000240000 0xffffc0000fc0003c 0xdbffff00003f0000

def z916 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf033f039 0x93c0fcf3f3c0cfc0

def z917 : W := mkw 0x9d188062ed288280 0x227462018bb4a20a 0xfff8c0e3fffc03fd 0xdfffe3038ffff00f

def z918 : W := mkw 0x602428db00000002 0x058090a36c000000 0xf03f3cff0000003a 0x97c0fcf3fc000000

def z919 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc0c303fffc0fff 0xffff030c0ffff03f

def z920 : W := mkw 0xddbfc062fdbc8284 0xb376ff018bf6f20a 0xffffc3e3fffc0fff 0xffffff0f8ffff03f

def z921 : W := mkw 0xeff6ffdb00c42462 0x8fbfdbff6c031091 0xffffffff01fc0fff 0xfffffffffc07f03f

def z922 : W := mkw 0x702d28b4f43ad301 0x15c0b4a2d3d0eb4c 0xf03f3cfcfe3ff33b 0xf7c0fcf3f3f8ffcc

def z923 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xfffff000ffff803f 0xfbffffc003fffe00

def z924 : W := mkw 0x10090024f972f701 0x5040240093e5cbdc 0x00000000f1f3f301 0x2000000003c7cfcc

def z925 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff00000ffe 0xbffffffffc00003f

def z926 : W := mkw 0xdd3c8000ed280004 0x9374f20003b4a000 0xfff8c000fffc003d 0xdbffe30003fff000

def z927 : W := mkw 0xddbfc020fdbc8204 0x9376ff0083f6f208 0xffffc0e0fffc033d 0xdfffff0383fff00c

def z928 : W := mkw 0xd9250000b9100000 0x1364940002e44000 0xffc70000ffc0003d 0x5bff1c0003ff0000

def z929 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff003c03fe 0x9ffffffffc00f00f

def z930 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf033f328 0x97c0fcf3f3c0cfcc

def z931 : W := mkw 0x702d28b4f43ad381 0x35c0b4a2d3d0eb4e 0xf03f3cfcf03ff3fb 0xb7c0fcf3f3c0ffcf

def z932 : W := mkw 0xedb6e8900d8c0004 0x87b6dba240363000 0xfffffcfc0fcc003e 0xdffffff3f03f3000

def z933 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff000c0cfe 0xdffffffffc003033

def z934 : W := mkw 0xddbfc009fdbc0004 0x9376ff0027f6f000 0xffffc01ffffc003d 0xdfffff007ffff000

def z935 : W := mkw 0x9d9bc024fdbed305 0x92766f0093f6fb4c 0x0fc0c000fffff305 0x683f030003ffffcc

def z936 : W := mkw 0x66f6ffdb02436c02 0xcd9bdbff6c090db0 0x003fffff0003fc02 0xa400fffffc000ff0

def z937 : W := mkw 0xbb003a00ab034800 0x02ec00e802ac0d20 0xffc03f00ffc3fc3f 0x7bff00fc03ff0ff0

def z938 : W := mkw 0xefb6fadb00000002 0x8fbedbeb6c000000 0xfffff0ff0000003c 0x9fffffc3fc000000

def z939 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff0000002c 0x1bfffffffc000000

def z940 : W := mkw 0x10090024f9b6d305 0x1040240093e6db4c 0x00000000f1f3f301 0x2000000003c7cfcc

def z941 : W := mkw 0xefb6fadb00000002 0x8fbedbeb6c000000 0xfe3f30fc00000020 0x1bf8fcc3f0000000

def z942 : W := mkw 0x64b6e89000000000 0x8592dba240000000 0xf03ffcfc0000003a 0x97c0fff3f0000000

def z943 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03ffcfff03ff3fb 0xb7c0fff3ffc0ffcf

def z944 : W := mkw 0xddbfc0f6fdbc9385 0xb776ff03dbf6f24e 0xffffc0fffffc03fd 0xdfffff03fffff00f

def z945 : W := mkw 0xdd3c8000ed280004 0x9374f20003b4a000 0xfff80000cfc00024 0x5bffe000033f0000

def z946 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc000fffc0028 0x9bffff0003fff000

def z947 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xfff8c000fffc0025 0x5bffe30003fff000

def z948 : W := mkw 0x99080000ed280000 0x0264200003b4a000 0xffc00000fffc003d 0x5bff000003fff000

def z949 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03fffff0000003e 0x97c0fffffc000000

def z950 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc00300ffc00c3f 0x7bff000c03ff0030

def z951 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x00000f0000007c00 0x0000003c000001f0

def z952 : W := mkw 0xedf6ed9900000000 0x87b7dbb664000000 0xffffffff0000003e 0x9ffffffffc000000

def z953 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfc3033f30a 0xb7c0fcf3f0c0cfcc

def z954 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcc033f322 0xb7c0fcf3f300cfcc

def z955 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffcfff0000000c 0x9fffff3ffc000000

def z956 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xfe3f3cfcfe33f33f 0xfff8fcf3f3f8cfcc

def z957 : W := mkw 0xbb403f4bab436c02 0x4aed00fd2ead0db0 0xffc03f03ffc3fc3f 0x7bff00fc0fff0ff0

def z958 : W := mkw 0xefb6fad200000000 0x87bedbeb48000000 0xffffffff0000003e 0x9ffffffffc000000

def z959 : W := mkw 0xddbfc024fdbc9305 0x9376ff0093f6f24c 0xffffc000fffc033d 0xdbffff0003fff00c

def z960 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x00003c000003f000 0x000000f000000fc0

def z961 : W := mkw 0xeff6ffdb0d080006 0x8fbfdbff6c342000 0xffffffff0e00003e 0x9ffffffffc380000

def z962 : W := mkw 0xddbfc0b0fdbc8205 0x9776ff02c3f6f208 0xffffc0e0fffc003d 0xdbffff0383fff000

def z963 : W := mkw 0x10090024f6ffffe1 0x3040240093dbffff 0x00000000ffffffc1 0x6000000003ffffff

def z964 : W := mkw 0xeff6ffdb0b412c02 0xcfbfdbff6c2d04b0 0xffffffff3fc07c3f 0xfffffffffcff01f0

def z965 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffffce00003f 0xdfffffffff380000

def z966 : W := mkw 0xddbfc004fdbc1104 0x9376ff0013f6f044 0xffffcc1cfffc703d 0xdbffff3073fff1c0

def z967 : W := mkw 0xeff6ffdb02034802 0xcfbfdbff6c080d20 0xffffffff0003803e 0x9ffffffffc000e00

def z968 : W := mkw 0x22403fdb02412c02 0x4c8900ff6c0904b0 0x00003fff00000c02 0x040000fffc000030

def z969 : W := mkw 0x44bfc0ff54bc93e1 0x3512ff03fd52f24f 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z970 : W := mkw 0x8fd2d74b06cd2ce2 0xaa3f4b5d2c1b34b3 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z971 : W := mkw 0x22403f0402437d00 0x488900fc10090df4 0x00003f1c0003ff02 0x240000fc70000ffc

def z972 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03300ffc3fc25 0x7bff00cc03ff0ff0

def z973 : W := mkw 0xd9af4000f9b40000 0x1366bd0003e6d000 0xffffc000fffc003d 0xdbffff0003fff000

def z974 : W := mkw 0xcdb6c09000000000 0x8736db0240000000 0xffffc0fc0000003c 0x9fffff03f0000000

def z975 : W := mkw 0x22403f240243ff01 0x488900fc90090ffc 0x00003f000003ff02 0x200000fc00000ffc

def z976 : W := mkw 0x10090024f63bdb81 0x3040240093d8ef6e 0x00000000fe33f301 0x2000000003f8cfcc

def z977 : W := mkw 0x6634bad206090880 0x2598d2eb48182422 0xfe3fffff0e0c0cfe 0xdff8fffffc383033

def z978 : W := mkw 0x30092824f032d301 0x10c024a093c0cb4c 0x00003c00f033f303 0x200000f003c0cfcc

def z979 : W := mkw 0xafd2ff4b00000000 0x0abf4bfd2c000000 0xffffffff0000003e 0x9ffffffffc000000

def z980 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xf1ffffff0000000a 0x97c7fffffc000000

def z981 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xfff83fe0ffc3fc3f 0xffffe0ff83ff0ff0

def z982 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03ffcfcf03ff33f 0xf7c0fff3f3c0ffcc

def z983 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x0000ff03003fffd7 0xe40003fc0c00ffff

def z984 : W := mkw 0x0418802044288200 0x001062008110a208 0x0e38f3e3ce3f8ff7 0xec38e3cf8f38fe3f

def z985 : W := mkw 0xeff6ffdb02436c02 0xcfbfdbff6c090db0 0xffffffffce03fc3f 0xffffffffff380ff0

def z986 : W := mkw 0x66f6ffdb00000000 0x059bdbff6c000000 0xffffffff0000003e 0x9ffffffffc000000

def z987 : W := mkw 0x10090024ff7bff81 0x7040240093fdeffe 0x00000000ffffffc1 0x6000000003ffffff

def z988 : W := mkw 0xddb7c000bd9c0004 0x9376df0002f67000 0xffc7c0003ffc001d 0xdbff1f0000fff000

def z989 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf1ff3cfcf1f3f33f 0xf7c7fcf3f3c7cfcc

def z990 : W := mkw 0x44bfc0f654bc9385 0xb512ff03d952f24e 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z991 : W := mkw 0x8fd2d74b0f492c82 0xea3f4b5d2c3d24b2 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z992 : W := mkw 0xbb403f90ab436c00 0x4eed00fe42ad0db0 0xffc03ffcffc3fc3f 0x7fff00fff3ff0ff0

def z993 : W := mkw 0x99010000b9940004 0x1264040002e65000 0xffc00000ffc0003d 0x5bff000003ff0000

def z994 : W := mkw 0xeff6ffdb0b436c02 0xcfbfdbff6c2d0db0 0xffffffff0fc3fc3e 0xfffffffffc3f0ff0

def z995 : W := mkw 0xef34bad200000002 0x8fbcd2eb48000000 0xfe3fffff0000003e 0x9ff8fffffc000000

def z996 : W := mkw 0x60a6689900000000 0x058299a264000000 0xf03ffcff0000003a 0x97c0fff3fc000000

def z997 : W := mkw 0xeff6ffdb02412c02 0x8fbfdbff6c0904b0 0xffffffffffc3fc3f 0xffffffffffff0ff0

def z998 : W := mkw 0x10090024f072f701 0x1040240093c1cbdc 0x00000000f1f3ff01 0x6000000003c7cffc

def z999 : W := mkw 0x6434a8d200000002 0x8590d2a348000000 0xf03f3cfc0000003a 0x97c0fcf3f0000000

def z1000 : W := mkw 0xddbec000edac0004 0x9376fb0003b6b000 0xffffc000cfcc003c 0xdbffff00033f3000

def z1001 : W := mkw 0x9983400db9941160 0x02660d0036e65045 0xffc7c01ffffc03fd 0xdfff1f007ffff00f

def z1002 : W := mkw 0xcdb6c0000d8c0004 0x8336db0000363000 0xfff8c0000fcc0024 0x5bffe300003f3000

def z1003 : W := mkw 0xedb6e8db00000002 0x87b6dba36c000000 0xfffffcff0000003e 0x9ffffff3fc000000

def z1004 : W := mkw 0x8fd2d74b0fcd2ce4 0xa23f4b5d2c3f34b3 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z1005 : W := mkw 0x22403ff60243ff81 0x6c8900ffd8090ffe 0x00003fff0003ffc2 0x240000fffc000fff

def z1006 : W := mkw 0x602528b41012d301 0x058094a2d0404b4c 0xf03f3cfc3033f33b 0xb7c0fcf3f0c0cfcc

def z1007 : W := mkw 0x99824000a9840004 0x8266090002a61000 0xffc00000ffc0003d 0x5bff000003ff0000

def z1008 : W := mkw 0x10090024f932d301 0x1040240093e4cb4c 0x00000000fff3f301 0x6000000003ffcfcc

def z1009 : W := mkw 0xe9e66d9900000002 0x8fa799b664000000 0xf1ffffff0000003e 0x97c7fffffc000000

def z1010 : W := mkw 0xf9e76d9db9d67561 0x5fe79db676e759d5 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z1011 : W := mkw 0xeff6ffdb00402402 0x8fbfdbff6c010090 0xffffffff00007c3e 0xbffffffffc0001f0

def z1012 : W := mkw 0x702d28b4f0b6d301 0x15c0b4a2d3c2db4c 0xf03f3cfcf1fff33b 0xf7c0fcf3f3c7ffcc

def z1013 : W := mkw 0x10090024ffbfdb85 0x3040240093feff6e 0x00000000ffffffc1 0x6000000003ffffff

def z1014 : W := mkw 0x702c28b4e022d301 0x15c0b0a2d3808b4c 0xf03f3cfcc003f33a 0xb7c0fcf3f3000fcc

def z1015 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf033f329 0x33c0fcf3f3c0cfcc

def z1016 : W := mkw 0xddbfc0dffdbc1166 0x9776ff037ff6f045 0xffffc0fffffc03fd 0xdfffff03fffff00f

def z1017 : W := mkw 0x10090024f4bed305 0x1040240093d2fb4c 0x00000000f03ff301 0x2000000003c0ffcc

def z1018 : W := mkw 0xbb403f42ab436c80 0x6aed00fd0aad0db2 0xffc03f03ffc3fcff 0x7bff00fc0fff0ff3

def z1019 : W := mkw 0x32403f00a2436c00 0x00c900fc02890db0 0xffc03f00ffc3fc3f 0x7bff00fc03ff0ff0

def z1020 : W := mkw 0xddbfc004fdbc1104 0x9376ff0013f6f044 0xffffcf1ffffc7fff 0xffffff3c7ffff1ff

def z1021 : W := mkw 0xddbfc0fbfdbc8286 0xb776ff03eff6f20a 0xffffc0fffffc03fd 0xdfffff03fffff00f

def z1022 : W := mkw 0x30092824f032d300 0x00c024a093c0cb4c 0xf03f3cfcf033f33b 0xb7c0fcf3f3c0cfcc

def z1023 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc000ffc0003c 0x9bffff0003ff0000

def z1024 : W := mkw 0x0618926246298a80 0x201862498918a62a 0x0e38f3e3ce3f8fe4 0xcc38e3cf8f38fe3f

def z1025 : W := mkw 0xf9e76d9db9d67562 0xcfe79db676e759d5 0xf1c70c1c31c07008 0x13c71c3070c701c0

def z1026 : W := mkw 0xeff6ffdb0f492c82 0xefbfdbff6c3d24b2 0xffffffff0fcc0cfe 0xdffffffffc3f3033

def z1027 : W := mkw 0xddbfc042fdbc0004 0x9376ff010bf6f000 0xffffc0e3fffc003d 0xdfffff038ffff000

def z1028 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc0c000fffc003d 0xdbff030003fff000

def z1029 : W := mkw 0x10090024f0b6d361 0x1040240093c2db4d 0x00000000f03ff3c1 0x2000000003c0ffcf

def z1030 : W := mkw 0x66b6fadb00000002 0x859adbeb6c000000 0xfe3fffff0000003e 0x9ff8fffffc000000

def z1031 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00000000f03fffc1 0x6000000003c0ffff

def z1032 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc0ff03ffcffcff 0x7bff03fc0fff3ff3

def z1033 : W := mkw 0xeff6ffdb00c42462 0x8fbfdbff6c031091 0xffffffff31cc7cff 0xfffffffffcc731f3

def z1034 : W := mkw 0xddbfc020fdbec205 0x9376ff0083f6fb08 0xffffc000ffff803d 0xdbffff0003fffe00

def z1035 : W := mkw 0x6434a89000000000 0x0590d2a240000000 0xfe3ffcfc0000003e 0x9ff8fff3f0000000

def z1036 : W := mkw 0x44bfc06f54bc93e4 0xb112ff01bd52f24f 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z1037 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc303fffc003f 0xdfffff0c0ffff000

def z1038 : W := mkw 0x54bfc000f4bc0000 0x1152ff0003d2f000 0xffffc000fffc003d 0xdbffff0003fff000

def z1039 : W := mkw 0xeff6ffdb06090882 0xafbfdbff6c182422 0xffffffffce0f8cff 0xffffffffff383e33

def z1040 : W := mkw 0xeff6ffdb0b010802 0xcfbfdbff6c2c0420 0xffffffff0e00003e 0x9ffffffffc380000

def z1041 : W := mkw 0x702d28b4fd3ad305 0x15c0b4a2d3f4eb4c 0xf03f3cfcfe33f33b 0xb7c0fcf3f3f8cfcc

def z1042 : W := mkw 0xddbfc000fdbe4004 0x9376ff0003f6f900 0xffffc000fffff03d 0xfbffff0003ffffc0

def z1043 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffff3ffc0000003e 0x1bfffcfff0000000

def z1044 : W := mkw 0x22403f6f0243ffe0 0x688900fdbc090fff 0x00003fff0003ffc2 0x240000fffc000fff

def z1045 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffff0000fff00039 0x9bfffc0003ffc000

def z1046 : W := mkw 0xd9af4000fdbc0004 0x9366bd0003f6f000 0xffc70000fffc003d 0x5bff1c0003fff000

def z1047 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffc7c000fffc000d 0x5bff1f0003fff000

def z1048 : W := mkw 0xeff6ffdb02010802 0x8fbfdbff6c080420 0xffffffff0e000c3e 0xdffffffffc380030

def z1049 : W := mkw 0xdd348000a9000000 0x8374d20002a40000 0xfff80000ffc0003d 0x5bffe00003ff0000

def z1050 : W := mkw 0x22403f0402437d60 0x488900fc10090df5 0x00003f000003ffc2 0x200000fc00000fff

def z1051 : W := mkw 0xeff6ffdb06090882 0xafbfdbff6c182422 0xffffffff0e00003e 0x9ffffffffc380000

def z1052 : W := mkw 0xdd3d8000fd380000 0x1374f60003f4e000 0xffffc000fffc003d 0xdbffff0003fff000

def z1053 : W := mkw 0x64f6eddb00000002 0x8593dbb76c000000 0xf1ffffff0000003e 0x97c7fffffc000000

def z1054 : W := mkw 0x10090024f43ad301 0x1040240093d0eb4c 0x00000000fe3ff301 0x6000000003f8ffcc

def z1055 : W := mkw 0x60642d9900000000 0x058190b664000000 0xf03f3fff0000003a 0x97c0fcfffc000000

def z1056 : W := mkw 0x702d2890f0324000 0x15c0b4a243c0c900 0xf03f3cfcf033f03b 0xb7c0fcf3f3c0cfc0

def z1057 : W := mkw 0xeff6ffdb02010802 0x8fbfdbff6c080420 0xffffffffce03803e 0x9fffffffff380e00

def z1058 : W := mkw 0xddbfc004fdbc1164 0x9376ff0013f6f045 0xffffc000fffc03fd 0xdbffff0003fff00f

def z1059 : W := mkw 0xddbfc062fdbc8284 0xb376ff018bf6f20a 0xfffff0e3ffff83ff 0xffffffc38ffffe0f

def z1060 : W := mkw 0xefb6fadb00000002 0x8fbedbeb6c000000 0xfe3ffcff0000003a 0x9ff8fff3fc000000

def z1061 : W := mkw 0x22403f9902436c02 0x4c8900fe64090db0 0x00003f1c0003fc02 0x200000fc70000ff0

def z1062 : W := mkw 0xb9402d00a9426400 0x02e500b402a50990 0xffc03f00ffc3fc3f 0x7bff00fc03ff0ff0

def z1063 : W := mkw 0xef74bfdb00000002 0x8fbdd2ff6c000000 0xfe3f3fff0000003a 0x9ff8fcfffc000000

def z1064 : W := mkw 0xbb003a00ab436c00 0x4aec00e802ad0db0 0xffc03000ffc3fc3d 0x7bff00c003ff0ff0

def z1065 : W := mkw 0xddbfc020fdbc8284 0xb376ff0083f6f20a 0xffffc000fffc03fd 0xdbffff0003fff00f

def z1066 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xfffffcfc0000003c 0x9bfffff3f0000000

def z1067 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03f3cfc0030033b 0xb7c0fcf3f000c00c

def z1068 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc000ffcc002c 0x5bffff0003ff3000

def z1069 : W := mkw 0x44bfc0ff54bc93e2 0xa512ff03fd52f24f 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z1070 : W := mkw 0xb9002800ab436c00 0x42e400a002ad0db0 0xffc03c00ffc3fc3f 0x7bff00f003ff0ff0

def z1071 : W := mkw 0x70252894b0125100 0x05c094a252c04944 0xf03f3cfcf033f33b 0xb7c0fcf3f3c0cfcc

def z1072 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc000fffc0ffd 0xfbffff0003fff03f

def z1073 : W := mkw 0xddbfc0d2fdbc0006 0x9776ff034bf6f000 0xffffc0e0fffc003d 0xdbffff0383fff000

def z1074 : W := mkw 0x22403f4202436c80 0x688900fd08090db2 0x00003f030003fcc2 0x200000fc0c000ff3

def z1075 : W := mkw 0x9d92c000a9000000 0x82764b0002a40000 0xffc0c000ffc0003d 0x5bff030003ff0000

def z1076 : W := mkw 0xebe67fdb00000002 0x8faf99ff6c000000 0xf1ff3fff0000003a 0x97c7fcfffc000000

def z1077 : W := mkw 0x99090000f9300000 0x1264240003e4c000 0xffc00000fff0003d 0x5bff000003ffc000

def z1078 : W := mkw 0xeff6ffdb0fcd2c06 0xcfbfdbff6c3f34b0 0xffffffff0fcc0c3e 0xdffffffffc3f3030

def z1079 : W := mkw 0x10090024f273ff01 0x5040240093c9cffc 0x00000000f033ff01 0x2000000003c0cffc

def z1080 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03f00ffc3f03e 0x1bff00fc03ff0fc0

def z1081 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00000000f033f313 0xa400000003c0cfcc

def z1082 : W := mkw 0x8fd2d74b0fcd2ce0 0x6a3f4b5d2c3f34b3 0x0fc0c3030fcc0cc4 0x483f030c0c3f3033

def z1083 : W := mkw 0x64b6e8db00000002 0x8592dba36c000000 0xf03fccff00000008 0x97c0ff33fc000000

def z1084 : W := mkw 0x22403f200243ee80 0x688900fc80090fba 0x00003f000003ffc2 0x200000fc00000fff

def z1085 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03f03ffc3ffff 0x7fff00fc0fff0fff

def z1086 : W := mkw 0xeb243a9000000000 0x0fac90ea40000000 0xfe3f3cfc0000003a 0x9ff8fcf3f0000000

def z1087 : W := mkw 0xdd3c8000ed280004 0x9374f20003b4a000 0xfff80000ffc00028 0x1bffe00003ff0000

def z1088 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3cfcf003f03a 0x97c0fcf3f3c00fc0

def z1089 : W := mkw 0xddb6c000ad8c0004 0x9376db0002b63000 0xffc0c0000fcc0004 0x5bff0300003f3000

def z1090 : W := mkw 0x60e66d9900000000 0x058399b664000000 0xf1ff3cfc0000003a 0x97c7fcf3f0000000

def z1091 : W := mkw 0xeff6ffdb04080002 0x8fbfdbff6c102000 0xffffffff0e0c003e 0xdffffffffc383000

def z1092 : W := mkw 0x44bfc0bd54bc9365 0x9512ff02f552f24d 0x003fc0ff003c03c0 0x8400ff03fc00f00f

def z1093 : W := mkw 0xefb6fadb00000002 0x8fbedbeb6c000000 0xfe3ff3ff00000036 0x9ff8ffcffc000000

def z1094 : W := mkw 0xeff6ffdb09402402 0xcfbfdbff6c250090 0xffffffff01c0003e 0x9ffffffffc070000

def z1095 : W := mkw 0x9d92c000ad8c0004 0x82764b0002b63000 0xffc0c0003fcc000c 0x5bff030000ff3000

def z1096 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff003c003f 0xdffffffffc00f000

def z1097 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffff0000fffc0029 0x5bfffc0003fff000

def z1098 : W := mkw 0x2658bf62466bee80 0x689962fd8919afba 0x0038ffe3003fffc2 0xa400e3ff8c00ffff

def z1099 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03f00ffc3fc2a 0x3bff00fc03ff0ff0

def z1100 : W := mkw 0xddbec000edac0004 0x9376fb0003b6b000 0xfff8c000cffc0035 0xdbffe300033ff000

def z1101 : W := mkw 0x22403f0902436c00 0x488900fc24090db0 0x00003f1f0003fc02 0x240000fc7c000ff0

def z1102 : W := mkw 0x22403fbd0243ff61 0x4c8900fef4090ffd 0x00003fff0003ffc2 0x240000fffc000fff

def z1103 : W := mkw 0xbb403f09ab436c60 0x4aed00fc26ad0db1 0xffc03f03ffc3fcff 0x7bff00fc0fff0ff3

def z1104 : W := mkw 0xddbfc024fdbed305 0x9376ff0093f6fb4c 0xfffff0e0fffff33f 0xffffffc383ffffcc

def z1105 : W := mkw 0xeff6ffdb00402402 0x8fbfdbff6c010090 0xffffffff01c00c3e 0xdffffffffc070030

def z1106 : W := mkw 0xeff6ffdb00840062 0x8fbfdbff6c021001 0xffffffff000c00fe 0x9ffffffffc003003

def z1107 : W := mkw 0x62643f9002436c00 0x4d8990fe40090db0 0xf03f3ffc0003fc3a 0xb7c0fcfff0000ff0

def z1108 : W := mkw 0xd92c0000e9200000 0x1364b00003a48000 0xfff80000ffc0003d 0x5bffe00003ff0000

def z1109 : W := mkw 0xef34bad200000002 0x8fbcd2eb48000000 0xfe3f30fc00000020 0x9ff8fcc3f0000000

def z1110 : W := mkw 0xeff6ffdb0dcc2466 0x8fbfdbff6c373091 0xffffffff0fcc0cfe 0xdffffffffc3f3033

def z1111 : W := mkw 0x62243a9000000000 0x058890ea40000000 0xfe3f3ffc0000003e 0x9ff8fcfff0000000

def z1112 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03c00ffc3f03b 0x3bff00f003ff0fc0

def z1113 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffffc003803f 0xbfffffffff000e00

def z1114 : W := mkw 0x0208122042218a00 0x0008204881088628 0x0e38f3e3ce3f8ff7 0xec38e3cf8f38fe3f

def z1115 : W := mkw 0xddbfc009fdbc0064 0x9376ff0027f6f001 0xffffc003fffc00fd 0xdbffff000ffff003

def z1116 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc000003fc0000c 0x5bff000000ff0000

def z1117 : W := mkw 0xedf6eddb00000002 0x8fb7dbb76c000000 0xffffccff0000003c 0x9fffff33fc000000

def z1118 : W := mkw 0xb9402d00ab436c00 0x4ae500b402ad0db0 0xffc00c00ffc3fc3d 0x7bff003003ff0ff0

def z1119 : W := mkw 0x44bfc0ff54bc9307 0x9512ff03fd52f24c 0x003fc0ff003c0300 0x8400ff03fc00f00c

def z1120 : W := mkw 0xddbfc0b4fdbc9305 0x9776ff02d3f6f24c 0xffffccfcfffc733f 0xffffff33f3fff1cc

def z1121 : W := mkw 0x702d28b4f9b6d305 0x15c0b4a2d3e6db4c 0xf03f3cfcf1f3f33b 0xb7c0fcf3f3c7cfcc

def z1122 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc00f00ffc3fc0d 0x7bff003c03ff0ff0

def z1123 : W := mkw 0xeff6ffdb0f8d0886 0xafbfdbff6c3e3422 0xffffffff0fcc0cfe 0xdffffffffc3f3033

def z1124 : W := mkw 0xbb403f00a9024000 0x0aed00fc02a40900 0xffc03f00ffc3f03f 0x7bff00fc03ff0fc0

def z1125 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7cf1f31fc7fcc 0xc4071f3c7cc7f1ff

def z1126 : W := mkw 0xddbfc04bfdbc0006 0x9376ff012ff6f000 0xffffc003fffc003d 0xdbffff000ffff000

def z1127 : W := mkw 0xeff6ffdb06090882 0xafbfdbff6c182422 0xffffffff0e3c0fff 0xfffffffffc38f03f

def z1128 : W := mkw 0xddbfc020fdbc8204 0x9376ff0083f6f208 0xfffff0e0ffff803d 0xdbffffc383fffe00

def z1129 : W := mkw 0x22483f204263ee00 0x488920fc81098fb8 0x00383fe0c033ff33 0xa400e0ff8300cffc

def z1130 : W := mkw 0x22403fff0243ff03 0x4c8900fffc090ffc 0x00003fff0003ff02 0x240000fffc000ffc

def z1131 : W := mkw 0x602d28b450309300 0x0580b4a2d140c24c 0xf03f3cfcf033f33b 0xb7c0fcf3f3c0cfcc

def z1132 : W := mkw 0x10cb452df0f6f761 0x10432d14b7c3dbdd 0x01c0c303f1ffffc5 0x6007030c0fc7ffff

def z1133 : W := mkw 0xbb003a00ab034800 0x4aec00e802ac0d20 0xffc03c00ffc3f03f 0x7bff00f003ff0fc0

def z1134 : W := mkw 0xddbfc0b4fdbc9305 0x9776ff02d3f6f24c 0xfffff0fcffff833f 0xffffffc3f3fffe0c

def z1135 : W := mkw 0xeff6ffdb02010802 0x8fbfdbff6c080420 0xffffffffce3f8fff 0xffffffffff38fe3f

def z1136 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3ffff033fffb 0xb7c0fcffffc0cfff

def z1137 : W := mkw 0x64b6e8db00000002 0x8592dba36c000000 0xf03ff0ff00000020 0x97c0ffc3fc000000

def z1138 : W := mkw 0xedf6eddb00000002 0x8fb7dbb76c000000 0xf1fffcff0000003a 0x97c7fff3fc000000

def z1139 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03f3cfc3000703b 0xb7c0fcf3f0c001c0

def z1140 : W := mkw 0x60642d9000000000 0x058190b640000000 0xf1ff3ffc0000003e 0x97c7fcfff0000000

def z1141 : W := mkw 0x60a6689900000002 0x858299a264000000 0xf03f3cfc0000003a 0x97c0fcf3f0000000

def z1142 : W := mkw 0xcdbec0004dac0004 0x8336fb000136b000 0xffffc000cffc003d 0xdbffff00033ff000

def z1143 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03f00ffffffff 0x7bff00fc03ffffff

def z1144 : W := mkw 0xebe67f9900000002 0x8faf99fe64000000 0xffff3ffc0000003e 0x9ffffcfff0000000

def z1145 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffffc000fffc033f 0xffffff0003fff00c

def z1146 : W := mkw 0xddb7c000bd9c0004 0x9376df0002f67000 0xffc700003fc00008 0x1bff1c0000ff0000

def z1147 : W := mkw 0x0610924202010800 0x0018424908080420 0x0e38f3e3ce3f8ff7 0xec38e3cf8f38fe3f

def z1148 : W := mkw 0x6434a8d200000000 0x0590d2a348000000 0xf03ffcff0000003a 0x97c0fff3fc000000

def z1149 : W := mkw 0x22413f0412537d00 0x488904fc10494df4 0x00073f1c3033ff1b 0xa4001cfc70c0cffc

def z1150 : W := mkw 0xddbec000edac0004 0x9376fb0003b6b000 0xfff80000cfc00020 0x1bffe000033f0000

def z1151 : W := mkw 0x702c28b0e022c200 0x05c0b0a2c3808b08 0xf03f3cfcf033f33b 0xb7c0fcf3f3c0cfcc

def z1152 : W := mkw 0xcdb6c0db00000002 0x8736db036c000000 0xf1ffc0ff00000008 0x97c7ff03fc000000

def z1153 : W := mkw 0x62243ad200000002 0x0d8890eb48000000 0xf03f3cfc0000003a 0x97c0fcf3f0000000

def z1154 : W := mkw 0xe9e66d9900000002 0x8fa799b664000000 0xf1ff3cfc00000028 0x13c7fcf3f0000000

def z1155 : W := mkw 0x44b6c0db00000002 0x8512db036c000000 0xf03fc0ff00000038 0x97c0ff03fc000000

def z1156 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffff3fff0000002a 0x1ffffcfffc000000

def z1157 : W := mkw 0x99010000b9940000 0x0264040002e65000 0xffc00000fffc003d 0x5bff000003fff000

def z1158 : W := mkw 0x12091224f233db01 0x1048244893c8cf6c 0x0e003300fe33ff37 0x683800cc03f8cffc

def z1159 : W := mkw 0xe9642d9000000000 0x0fa590b640000000 0xf1ff3cfc0000003a 0x97c7fcf3f0000000

def z1160 : W := mkw 0x702d28b4f032d301 0x15c0b4a2d3c0cb4c 0xf03f3ffcf033ff3f 0xf7c0fcfff3c0cffc

def z1161 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03f0cfc00000008 0x97c0fc33f0000000

def z1162 : W := mkw 0xddbfc000fdbc0004 0x9376ff0003f6f000 0xffff0000ffc0003d 0x5bfffc0003ff0000

def z1163 : W := mkw 0x22403fb00243ee01 0x4c8900fec0090fb8 0x00003fe00003fc02 0x200000ff80000ff0

def z1164 : W := mkw 0xddbfc042fdbc0084 0xb376ff010bf6f002 0xffffc003fffc00fd 0xdbffff000ffff003

def z1165 : W := mkw 0xff3cbaf2ef2bca85 0xb7fcf2ebcbbcaf2a 0xfe3830e0ce038020 0x1bf8e0c383380e00

def z1166 : W := mkw 0x6024289000000000 0x058090a240000000 0xf03f3cfcc003803b 0xb7c0fcf3f3000e00

def z1167 : W := mkw 0xe9e66d9900000002 0x8fa799b664000000 0xf1ff0cfc00000008 0x97c7fc33f0000000

def z1168 : W := mkw 0xddbfc020fdbc8204 0x9376ff0083f6f208 0xfffff3e3ffff8fff 0xffffffcf8ffffe3f

def z1169 : W := mkw 0x60a6689000000000 0x058299a240000000 0xf1fffcfc0000003e 0x97c7fff3f0000000

def z1170 : W := mkw 0x0041050410503500 0x00010414104140d4 0x01c7cf1f31fc7fdf 0xe4071f3c7cc7f1ff

def z1171 : W := mkw 0xcdbfc00054bc0000 0x8336ff000152f000 0xffffc000fffc003d 0xdbffff0003fff000

def z1172 : W := mkw 0xd9a64000a9000000 0x8366990002a40000 0xffc70000ffc0003d 0x5bff1c0003ff0000

def z1173 : W := mkw 0x99824000a9840000 0x0266090002a61000 0xffc0c000ffcc003d 0x5bff030003ff3000

def z1174 : W := mkw 0xd9af4000f9b40004 0x9366bd0003e6d000 0xffff0000fff0003d 0xdbfffc0003ffc000

def z1175 : W := mkw 0xddb7c000bd9c0004 0x9376df0002f67000 0xffc7c000ffcc003d 0x5bff1f0003ff3000

def z1176 : W := mkw 0x99000000a9000000 0x0264000002a40000 0xffc03000ffc3803f 0x7bff00c003ff0e00

def z1177 : W := mkw 0x10090024f43ad381 0x3040240093d0eb4e 0x00000000f03ff3c1 0x2000000003c0ffcf

def z1178 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xfffffcff00000028 0x9ffffff3fc000000

def z1179 : W := mkw 0xedf6eddb00000002 0x8fb7dbb76c000000 0xf1ff0cfc00000008 0x13c7fc33f0000000

def z1180 : W := mkw 0x9d9bc000fdbc0000 0x02766f0003f6f000 0xffffc000fffc003d 0xdbffff0003fff000

def z1181 : W := mkw 0x10090024ffffffe0 0x6040240093ffffff 0x00000000ffffffc1 0x6000000003ffffff

def z1182 : W := mkw 0x22403f0002436c00 0x488900fc00090db0 0x00003f003003fc1b 0x200000fc00c00ff0

def z1183 : W := mkw 0x702528b4b012d301 0x15c094a2d2c04b4c 0xf03f3cfc3003f33a 0xb7c0fcf3f0c00fcc

def z1184 : W := mkw 0x702d28b4f4bed305 0x15c0b4a2d3d2fb4c 0xf03f3cfcf03ff33b 0xb7c0fcf3f3c0ffcc

def z1185 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03f00ffc3fc2c 0x5bff00fc03ff0ff0

def z1186 : W := mkw 0x9d188000ed280000 0x0274620003b4a000 0xfff80000ffc0003d 0x5bffe00003ff0000

def z1187 : W := mkw 0x22403f0902436c60 0x488900fc24090db1 0x00003f030003fcc2 0x200000fc0c000ff3

def z1188 : W := mkw 0x00c3450d10d43560 0x00030d14344350d5 0x01c7ff1ff1ffffff 0xe4071ffc7fc7ffff

def z1189 : W := mkw 0xd9a74000b9940004 0x93669d0002e65000 0xffc7c000fffc003d 0xdbff1f0003fff000

def z1190 : W := mkw 0x10090024f072f761 0x1040240093c1cbdd 0x00000000f033ffc1 0x2000000003c0cfff

def z1191 : W := mkw 0x62243a9002010800 0x058890ea40080420 0xfe3f3ffcce038c3f 0xfff8fcfff3380e30

def z1192 : W := mkw 0x8d92c0000d8c0004 0x82364b0000363000 0xffc0c0000fcc003c 0x5bff0300003f3000

def z1193 : W := mkw 0x10090024f032d301 0x1040240093c0cb4c 0x00000c00f033f31b 0x2000003003c0cfcc

def z1194 : W := mkw 0xeff6ffdb09840006 0x8fbfdbff6c261000 0xffffffff01c0003e 0x9ffffffffc070000

def z1195 : W := mkw 0x6674bfdb00000002 0x0d99d2ff6c000000 0xfe3fffff0000003e 0x9ff8fffffc000000

def z1196 : W := mkw 0x70252894b0125101 0x15c094a252c04944 0xf03f3cfcf003f03b 0xb7c0fcf3f3c00fc0

def z1197 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc03c00ffc3f03d 0x5bff00f003ff0fc0

def z1198 : W := mkw 0x502d0024f0309300 0x1140b40093c0c24c 0xf03f3cfcf033f33b 0xb7c0fcf3f3c0cfcc

def z1199 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff3000703f 0xbffffffffcc001c0

def z1200 : W := mkw 0xddbfc004fdbc1104 0x9376ff0013f6f044 0xffffc01cfffc033d 0xdfffff0073fff00c

def z1201 : W := mkw 0xebe67f9900000000 0x0faf99fe64000000 0xffffffff0000003e 0x9ffffffffc000000

def z1202 : W := mkw 0xedf6ed9900000002 0x8fb7dbb664000000 0xfffffcfc0000003e 0x9ffffff3f0000000

def z1203 : W := mkw 0xeff6ffdb00000002 0x8fbfdbff6c000000 0xffffffff0030033f 0xbffffffffc00c00c

def z1204 : W := mkw 0xe924289000000002 0x8fa490a240000000 0xf03f3cfc0000003a 0x97c0fcf3f0000000

def z1205 : W := mkw 0x99010004b9101100 0x0264040012e44044 0xffc70c1cfff0733f 0xffff1c3073ffc1cc

def z1206 : W := mkw 0x60e66d9900c42460 0x058399b664031091 0xf1ffffff01cc0cfe 0xd7c7fffffc073033

def z1207 : W := mkw 0xbb403f00ab436c00 0x4aed00fc02ad0db0 0xffc0ff03ffc3fc3f 0xffff03fc0fff0ff0

def z1208 : W := mkw 0xeff6ffdb00402462 0x8fbfdbff6c010091 0xffffffff00000cfe 0x9ffffffffc000033

def z1209 : W := mkw 0x9b001200ab436c00 0x426c004802ad0db0 0xffc03300ffc3fc3f 0x7bff00cc03ff0ff0

def z1210 : W := mkw 0xeff6ffdb06cd2ce2 0xafbfdbff6c1b34b3 0xffffffff0fcc0cfe 0xdffffffffc3f3033

def z1211 : W := mkw 0xefb6fad200000002 0x8fbedbeb48000000 0xfffffcfc0000003e 0x9ffffff3f0000000

def z1212 : W := mkw 0xddbfc00dfdbc1164 0x9376ff0037f6f045 0xffffc01cfffc003d 0xdbffff0073fff000

def z1213 : W := mkw 0xef74bfd200000002 0x8fbdd2ff48000000 0xffff3ffc0000003e 0x9ffffcfff0000000

def z1214 : W := mkw 0x702d28b4f0b6d361 0x15c0b4a2d3c2db4d 0xf03f3cfcf03ff3fb 0xb7c0fcf3f3c0ffcf

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z8,z5,z6]),(1,[z1,z2,z9,z7,z10,z6])],[(0,[z11,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z12,z4,z13,z6]),(0,[z1,z2,z14,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z15]),(1,[z1,z16,z7,z17,z5,z6]),(0,[z1,z2,z18,z7,z4,z17,z5]),(0,[z1,z19,z2,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z20,z21]),(0,[z22,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z23,z7,z4,z5,z6]),(0,[z1,z2,z7,z24,z10,z4,z6]),(0,[z1,z2,z7,z25,z4,z5,z6])],[(0,[z1,z2,z7,z26,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z27,z6])],[(0,[z1,z2,z28,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z29,z6]),(0,[z30,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z31,z6]),(0,[z1,z2,z32,z7,z33,z4,z6]),(0,[z1,z2,z7,z12,z4,z5,z34]),(0,[z1,z2,z35,z18,z7,z4,z5]),(0,[z1,z2,z7,z10,z4,z6,z36]),(0,[z1,z2,z7,z4,z37,z5,z6]),(0,[z1,z2,z38,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z39,z6,z36])],[(0,[z1,z2,z7,z4,z40,z5,z6]),(0,[z41,z1,z2,z7,z4,z5,z6]),(0,[z42,z1,z7,z43,z4,z5,z6]),(0,[z44,z1,z19,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z45,z6]),(0,[z1,z46,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z47]),(0,[z1,z2,z7,z4,z5,z6,z48]),(0,[z1,z49,z2,z7,z4,z5,z6])],[(0,[z50,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z51,z52,z7,z4,z5])],[(0,[z53,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z3,z4,z5]),(1,[z42,z1,z43,z4,z5,z6]),(0,[z42,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z18,z54,z7,z4,z5]),(0,[z1,z55,z56,z7,z4,z5,z6]),(0,[z1,z2,z57,z7,z4,z5,z6]),(0,[z58,z1,z2,z32,z7,z4,z6])]],
   [[(0,[z59,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z60,z17,z5,z6]),(0,[z1,z2,z7,z4,z5,z61,z6]),(0,[z42,z1,z2,z54,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z62]),(0,[z1,z16,z2,z7,z4,z5,z6]),(0,[z1,z2,z63,z7,z4,z5,z64]),(1,[z1,z2,z7,z4,z65,z6]),(0,[z1,z2,z7,z66,z10,z4,z6]),(0,[z1,z2,z67,z7,z10,z4,z6]),(0,[z1,z2,z68,z7,z5,z6,z48])],[(0,[z1,z2,z7,z69,z4,z5,z6])],[(0,[z1,z2,z7,z4,z70,z5,z6]),(0,[z1,z71,z2,z7,z4,z5,z6]),(0,[z1,z16,z72,z7,z4,z5,z6]),(0,[z1,z56,z2,z7,z10,z4,z6]),(0,[z1,z2,z73,z7,z4,z5,z6]),(0,[z1,z2,z74,z7,z4,z5,z6]),(0,[z1,z2,z67,z75,z7,z4,z5])],[(0,[z1,z2,z7,z76,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z77,z6]),(0,[z1,z2,z75,z7,z5,z6,z78]),(1,[z1,z2,z79,z4,z5,z6])],[(1,[z1,z2,z7,z4,z80,z6]),(1,[z81,z82,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z83]),(1,[z1,z2,z84,z7,z4,z5]),(0,[z85,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z32,z7,z86,z4,z6])],[(0,[z1,z2,z87,z7,z4,z5,z6]),(0,[z1,z2,z88,z4,z5,z6,z21])],[(0,[z89,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z90,z4,z5,z6]),(0,[z1,z91,z2,z7,z4,z5,z6]),(0,[z1,z2,z75,z7,z10,z4,z6]),(1,[z1,z2,z92,z4,z5,z6])],[(0,[z1,z93,z2,z32,z7,z4,z6]),(1,[z94,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z6]),(0,[z44,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z56,z2,z18,z7,z4,z5]),(0,[z1,z95,z2,z7,z4,z5,z6])],[(0,[z96,z1,z2,z7,z4,z5,z6]),(0,[z44,z1,z2,z7,z4,z5,z97]),(0,[z1,z2,z51,z18,z4,z5,z6]),(0,[z98,z1,z2,z7,z10,z4,z6]),(1,[z1,z2,z7,z10,z6,z78]),(0,[z1,z2,z99,z7,z4,z5,z6])],[(1,[z1,z2,z51,z7,z4,z65]),(0,[z1,z2,z51,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z100])],[(0,[z1,z2,z7,z7,z4,z5,z6])],[(0,[z1,z2,z7,z101,z4,z5,z6]),(0,[z102,z2,z7,z60,z4,z5,z6]),(0,[z103,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z104,z5,z6]),(0,[z1,z16,z2,z7,z105,z5,z6]),(0,[z1,z2,z7,z4,z106,z5,z6]),(0,[z1,z2,z75,z18,z7,z4,z5]),(0,[z1,z2,z51,z75,z7,z4,z5])],[(0,[z1,z2,z7,z107,z4,z5,z6]),(0,[z0,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z108,z5]),(0,[z1,z2,z7,z4,z5,z6,z109]),(0,[z1,z2,z110,z12,z4,z5,z6])],[(0,[z1,z2,z111,z7,z4,z5,z6]),(0,[z1,z2,z7,z112,z4,z5,z6]),(0,[z1,z2,z32,z113,z7,z4,z6]),(0,[z1,z2,z75,z7,z114,z4,z6])],[(0,[z115,z1,z2,z7,z4,z5,z6]),(0,[z116,z1,z2,z51,z7,z4,z5]),(1,[z1,z2,z7,z117,z4,z6]),(0,[z1,z55,z2,z7,z4,z5,z6]),(0,[z1,z2,z118,z7,z4,z5,z6]),(0,[z1,z2,z119,z7,z12,z4,z5]),(0,[z120,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z10,z10,z4,z6]),(0,[z1,z2,z32,z121,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z122])]],
   [[(0,[z1,z2,z123,z7,z4,z5,z6]),(0,[z124,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z125,z7,z4,z5,z6]),(0,[z1,z126,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z127,z4,z5,z6]),(1,[z1,z2,z7,z4,z39,z36])],[(0,[z128,z1,z2,z7,z4,z5,z6]),(0,[z129,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z130,z4,z5,z6]),(0,[z1,z2,z7,z131,z4,z5,z6]),(0,[z1,z132,z2,z7,z4,z5,z133]),(0,[z1,z16,z2,z7,z4,z5,z134]),(0,[z1,z72,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z135,z5,z6]),(0,[z1,z2,z9,z7,z10,z4,z6])],[(0,[z81,z1,z2,z7,z136,z5,z6]),(1,[z1,z2,z7,z4,z5,z137]),(0,[z1,z138,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z139,z6]),(0,[z140,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z12,z4,z141,z6]),(0,[z1,z19,z2,z51,z7,z4,z5]),(0,[z1,z2,z142,z7,z4,z5,z6]),(0,[z1,z143,z2,z7,z4,z5,z6]),(0,[z1,z2,z35,z7,z4,z39,z5])],[(0,[z1,z2,z7,z144,z4,z5,z6]),(0,[z1,z2,z7,z4,z145,z5,z6]),(0,[z1,z2,z9,z75,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z6,z146]),(0,[z1,z2,z110,z32,z7,z4,z6])],[(0,[z1,z147,z2,z7,z4,z5,z6]),(0,[z41,z102,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z148,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z149]),(0,[z1,z2,z33,z150,z4,z5,z6])],[(0,[z1,z2,z151,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z5,z152]),(0,[z1,z2,z67,z7,z4,z5,z78])],[(0,[z0,z1,z2,z153,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z154,z6]),(0,[z1,z72,z2,z18,z7,z4,z5]),(1,[z1,z2,z32,z7,z4,z6])]],
   [[(0,[z155,z1,z2,z7,z4,z5,z6]),(0,[z103,z1,z2,z7,z4,z13,z6])],[(0,[z1,z2,z18,z7,z4,z5,z156])],[(0,[z81,z2,z82,z7,z4,z5,z6]),(0,[z1,z157,z2,z7,z4,z5,z6]),(0,[z102,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z158,z4,z5,z6]),(0,[z1,z159,z2,z51,z7,z4,z5]),(0,[z1,z2,z7,z150,z10,z4,z6])],[(0,[z1,z2,z160,z7,z4,z5,z6]),(0,[z1,z2,z161,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z97,z146]),(0,[z1,z2,z88,z18,z4,z5,z6]),(0,[z1,z2,z18,z7,z10,z4,z6]),(0,[z1,z2,z7,z86,z5,z6,z78]),(0,[z1,z2,z7,z4,z5,z162,z6])],[(0,[z1,z2,z7,z4,z5,z163,z6]),(0,[z1,z2,z7,z4,z5,z164,z6]),(0,[z165,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z88,z7,z10,z4,z6])],[(0,[z1,z2,z7,z4,z5,z6,z166]),(0,[z1,z2,z7,z167,z4,z5,z6]),(0,[z103,z2,z7,z4,z13,z5,z6]),(0,[z1,z2,z168,z7,z4,z5,z6]),(0,[z1,z2,z169,z7,z4,z5,z6]),(1,[z1,z2,z170,z4,z5,z6])],[(0,[z1,z7,z105,z4,z17,z5,z6]),(0,[z1,z2,z7,z171,z4,z5,z6]),(0,[z1,z2,z7,z4,z65,z5,z6]),(0,[z1,z2,z7,z4,z172,z5,z6]),(0,[z1,z2,z173,z7,z4,z5,z6]),(0,[z1,z2,z9,z75,z7,z5,z6])],[(0,[z174,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z175,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z176,z6]),(1,[z1,z2,z32,z7,z4,z122]),(0,[z1,z2,z7,z177,z4,z5,z6])]],
   [[(0,[z102,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z5,z78])],[(0,[z1,z2,z7,z178,z4,z5,z6]),(0,[z1,z2,z179,z7,z4,z5,z6]),(0,[z1,z2,z180,z7,z4,z5,z6]),(0,[z1,z132,z2,z7,z4,z5,z181])],[(0,[z1,z2,z7,z4,z5,z182,z6]),(1,[z1,z2,z183,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z184]),(0,[z1,z2,z88,z18,z7,z4,z5]),(0,[z1,z2,z7,z185,z4,z5,z6])],[(0,[z186,z1,z2,z7,z4,z5,z6]),(0,[z42,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z10,z4,z6,z21]),(0,[z1,z187,z2,z7,z10,z4,z6]),(0,[z1,z2,z68,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z188,z5,z6])],[(0,[z189,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z190,z6])],[(0,[z81,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z191,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z192,z6]),(0,[z1,z2,z7,z4,z5,z193,z6]),(0,[z1,z2,z194,z7,z4,z5,z6]),(0,[z1,z2,z195,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z196])],[(0,[z81,z1,z93,z7,z4,z5,z6]),(0,[z197,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z17,z5,z6]),(0,[z1,z56,z2,z7,z4,z141,z6]),(0,[z1,z2,z7,z4,z5,z6,z198]),(0,[z1,z2,z7,z4,z199,z6,z64]),(0,[z1,z2,z18,z7,z4,z5,z152]),(0,[z200,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z32,z7,z4,z5]),(1,[z1,z2,z7,z4,z176,z6]),(0,[z1,z2,z7,z4,z5,z201,z6]),(0,[z1,z2,z9,z7,z4,z5,z78])]],
   [[(0,[z1,z2,z7,z4,z5,z202,z6]),(0,[z1,z2,z203,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z39,z6,z64]),(0,[z1,z2,z7,z10,z4,z4,z6]),(0,[z1,z2,z204,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z70,z6]),(0,[z1,z205,z2,z7,z4,z5,z6]),(0,[z42,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z206,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z207,z5,z6]),(0,[z1,z2,z7,z208,z4,z5,z6]),(0,[z1,z2,z209,z7,z4,z5,z6]),(0,[z1,z2,z210,z7,z4,z5,z6]),(1,[z1,z2,z32,z68,z7,z6]),(0,[z1,z2,z7,z92,z4,z5,z6])],[(0,[z1,z2,z7,z211,z4,z5,z6]),(0,[z1,z212,z2,z7,z4,z5,z6]),(0,[z42,z1,z2,z7,z4,z213,z6]),(0,[z1,z2,z214,z7,z4,z5,z6]),(0,[z1,z2,z215,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z216]),(0,[z1,z2,z217,z4,z5,z6,z78])],[(0,[z1,z2,z7,z4,z5,z218,z6]),(0,[z0,z1,z2,z7,z4,z5,z219]),(0,[z1,z2,z220,z7,z4,z5,z6]),(0,[z41,z1,z2,z32,z7,z4,z6]),(1,[z221,z2,z7,z4,z5,z77]),(0,[z222,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z150,z4,z5,z6])],[(0,[z223,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z5,z224]),(0,[z1,z2,z225,z7,z4,z5,z6]),(0,[z1,z2,z226,z7,z4,z5,z6]),(0,[z1,z132,z2,z43,z4,z5,z6]),(0,[z1,z2,z7,z4,z227,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z228]),(0,[z1,z46,z2,z32,z7,z4,z6]),(0,[z229,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z230,z6]),(0,[z1,z7,z4,z5,z97,z6,z152]),(0,[z1,z2,z7,z231,z4,z5,z6])],[(0,[z1,z2,z7,z232,z4,z5,z6]),(0,[z1,z2,z233,z7,z10,z4,z6]),(0,[z1,z234,z2,z7,z4,z5,z6]),(0,[z1,z2,z67,z35,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z6,z235]),(1,[z41,z2,z7,z108,z5,z6]),(0,[z41,z1,z2,z7,z108,z5,z6]),(0,[z1,z16,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z236]),(0,[z237,z1,z2,z51,z7,z4,z5]),(1,[z1,z2,z7,z10,z6,z48])]],
   [[(0,[z238,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z239,z4,z5,z6]),(0,[z1,z2,z160,z7,z4,z108,z6]),(0,[z1,z2,z240,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z241,z5,z6]),(0,[z1,z72,z2,z51,z7,z4,z5]),(0,[z1,z7,z4,z199,z5,z141,z6]),(0,[z1,z2,z7,z4,z5,z242,z6]),(0,[z1,z2,z7,z243,z4,z5,z6]),(0,[z1,z244,z2,z7,z4,z5,z6]),(0,[z1,z2,z18,z245,z7,z4,z5]),(0,[z1,z2,z246,z51,z7,z4,z5])],[(0,[z247,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z248,z7,z43,z4,z5]),(0,[z1,z2,z18,z7,z4,z5,z78])],[(0,[z1,z2,z7,z4,z199,z224,z6]),(0,[z50,z1,z2,z7,z4,z5,z146]),(0,[z1,z2,z249,z7,z4,z5,z6]),(0,[z1,z2,z110,z7,z4,z6,z64]),(0,[z1,z2,z7,z10,z5,z6,z48]),(0,[z1,z2,z32,z7,z4,z37,z6])],[(0,[z116,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z51,z7,z60,z4,z5]),(0,[z1,z2,z7,z10,z4,z224,z6]),(0,[z1,z2,z51,z7,z4,z199,z5]),(0,[z1,z2,z7,z12,z4,z5,z6])],[(0,[z250,z1,z2,z7,z4,z5,z6]),(0,[z0,z2,z153,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z97,z77]),(0,[z1,z2,z7,z4,z5,z251,z6]),(0,[z1,z2,z7,z10,z105,z4,z6]),(0,[z1,z2,z7,z86,z4,z5,z78])],[(0,[z1,z2,z252,z7,z4,z5,z6]),(1,[z1,z2,z253,z7,z4,z5]),(0,[z1,z2,z12,z4,z5,z6,z64])],[(0,[z1,z2,z7,z254,z4,z5,z6]),(0,[z255,z1,z2,z7,z4,z5,z6]),(0,[z256,z1,z2,z7,z4,z5,z6]),(0,[z44,z1,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z10,z86,z4,z6]),(0,[z1,z2,z92,z4,z5,z6,z78])],[(0,[z221,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z257]),(1,[z1,z2,z7,z258,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z259,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z260])],[(0,[z116,z1,z2,z18,z7,z4,z5]),(0,[z102,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z261,z7,z4,z5,z6]),(1,[z1,z72,z7,z105,z5,z6]),(0,[z1,z2,z262,z51,z7,z4,z5])],[(0,[z1,z2,z263,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z13,z141,z6]),(0,[z1,z2,z7,z4,z5,z6,z264]),(0,[z1,z16,z2,z18,z7,z4,z5]),(0,[z265,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z266,z5,z6]),(0,[z1,z2,z267,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z268]),(1,[z1,z2,z7,z4,z269,z6]),(0,[z270,z1,z2,z7,z4,z5,z6]),(0,[z1,z271,z2,z7,z4,z5,z6]),(0,[z1,z2,z32,z18,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z272])],[(0,[z1,z2,z7,z60,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z134]),(1,[z1,z2,z7,z4,z251,z6]),(0,[z1,z2,z273,z7,z4,z5,z6]),(0,[z274,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z275]),(0,[z1,z2,z276,z7,z4,z5,z6])],[(0,[z1,z2,z18,z7,z4,z5,z224]),(0,[z1,z2,z277,z7,z4,z5,z6]),(0,[z1,z2,z88,z150,z4,z5,z6])],[(0,[z1,z2,z82,z7,z10,z4,z6]),(0,[z1,z55,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z4,z278,z5,z6]),(0,[z115,z1,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z279,z4,z5,z6])],[(1,[z1,z2,z280,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z80,z6]),(0,[z1,z2,z7,z105,z60,z5,z6]),(0,[z1,z2,z32,z7,z12,z4,z6])]],
   [[(0,[z281,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z282,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z4,z5,z283]),(1,[z1,z2,z18,z4,z5,z228]),(0,[z284,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z170,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z285]),(0,[z1,z2,z7,z4,z5,z286,z6]),(0,[z1,z2,z32,z118,z7,z4,z6]),(0,[z1,z2,z7,z287,z4,z5,z6]),(0,[z1,z138,z2,z32,z7,z4,z6]),(0,[z1,z2,z288,z7,z4,z5,z6])],[(0,[z81,z1,z2,z7,z4,z80,z6]),(0,[z1,z19,z2,z7,z4,z5,z152]),(1,[z1,z2,z88,z5,z6,z21])],[(0,[z1,z289,z2,z7,z4,z5,z6]),(0,[z1,z2,z290,z32,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z36])],[(0,[z1,z2,z82,z18,z7,z4,z5]),(0,[z1,z2,z18,z7,z60,z4,z5]),(0,[z221,z1,z2,z7,z4,z5,z146]),(0,[z1,z2,z7,z4,z5,z6,z291]),(0,[z1,z2,z18,z7,z4,z199,z5]),(0,[z1,z2,z292,z7,z4,z5,z6])],[(0,[z1,z2,z32,z7,z4,z141,z6]),(0,[z1,z2,z293,z7,z4,z5,z6]),(0,[z1,z2,z7,z294,z4,z5,z6]),(0,[z1,z295,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z296,z5,z6]),(0,[z1,z2,z32,z7,z4,z77,z6]),(0,[z1,z2,z7,z4,z5,z134,z6]),(1,[z1,z2,z88,z7,z10,z6]),(0,[z1,z297,z2,z7,z4,z5,z6]),(0,[z1,z298,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z5,z48]),(0,[z1,z2,z67,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z299,z5,z6]),(1,[z1,z2,z7,z4,z300,z6]),(0,[z1,z2,z7,z4,z301,z5,z6]),(0,[z221,z50,z2,z7,z4,z5,z6]),(0,[z302,z1,z2,z7,z4,z5,z6]),(0,[z303,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z84,z7,z4,z5,z6]),(0,[z1,z2,z7,z304,z4,z5,z6]),(0,[z1,z305,z2,z7,z4,z5,z6])]],
   [[(1,[z1,z2,z306,z4,z5,z6])],[(0,[z1,z2,z54,z3,z4,z5,z6]),(0,[z1,z307,z2,z7,z4,z5,z6]),(0,[z1,z2,z308,z7,z4,z5,z6])],[(0,[z1,z309,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z310,z4,z5,z6]),(0,[z1,z2,z32,z7,z43,z4,z6]),(0,[z1,z55,z2,z7,z4,z199,z6]),(1,[z1,z2,z110,z12,z4,z6]),(0,[z1,z2,z51,z7,z150,z4,z5]),(0,[z311,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z312,z6]),(0,[z313,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z314,z7,z4,z5,z6]),(0,[z1,z72,z2,z7,z4,z241,z6]),(0,[z1,z2,z7,z315,z4,z5,z6]),(0,[z1,z2,z52,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z316]),(1,[z1,z2,z7,z317,z5,z6])],[(0,[z318,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z32,z153,z7,z4,z6]),(0,[z1,z2,z7,z4,z319,z5,z6]),(0,[z1,z2,z7,z4,z320,z5,z6]),(0,[z22,z1,z2,z51,z7,z4,z5])],[(0,[z2,z7,z60,z4,z108,z5,z6]),(0,[z321,z1,z2,z7,z4,z5,z6]),(0,[z1,z132,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z322,z5,z6]),(0,[z1,z2,z51,z323,z7,z4,z5]),(0,[z1,z2,z324,z51,z7,z4,z5]),(0,[z1,z2,z32,z7,z10,z5,z6]),(0,[z1,z2,z7,z325,z4,z5,z6])],[(0,[z0,z1,z2,z7,z4,z5,z326]),(0,[z2,z7,z4,z13,z5,z224,z6]),(0,[z1,z2,z32,z35,z7,z4,z6])],[(0,[z1,z2,z7,z4,z136,z5,z6]),(0,[z1,z327,z2,z7,z4,z5,z6]),(0,[z1,z93,z2,z7,z10,z4,z6]),(0,[z1,z2,z328,z7,z4,z5,z6]),(0,[z1,z2,z329,z7,z4,z5,z6]),(0,[z1,z55,z7,z4,z199,z5,z6]),(0,[z1,z2,z323,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z330,z6]),(0,[z1,z2,z7,z258,z4,z5,z6]),(0,[z1,z2,z7,z10,z5,z6,z78])]],
   [[(0,[z81,z1,z2,z7,z4,z5,z137]),(0,[z331,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z332,z6]),(0,[z1,z2,z51,z7,z4,z5,z6])],[(0,[z1,z2,z333,z7,z4,z5,z6]),(0,[z334,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z105,z4,z5]),(0,[z1,z2,z7,z4,z5,z97,z6]),(0,[z1,z2,z335,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z336,z4,z5]),(0,[z1,z2,z7,z337,z10,z4,z6]),(0,[z1,z2,z338,z7,z4,z5,z6])],[(0,[z94,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z339]),(0,[z103,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z340,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z341]),(0,[z1,z2,z7,z342,z4,z5,z6]),(0,[z1,z2,z57,z51,z7,z4,z5]),(0,[z1,z2,z32,z7,z4,z39,z6]),(0,[z1,z2,z343,z7,z4,z5,z6])],[(0,[z81,z1,z82,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z108,z5,z6]),(0,[z1,z16,z2,z51,z7,z4,z5]),(0,[z1,z2,z32,z7,z4,z6,z152]),(0,[z1,z2,z51,z7,z86,z4,z5]),(0,[z344,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z345,z4,z5,z6])],[(0,[z346,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z347,z5,z6]),(0,[z1,z2,z7,z348,z4,z5,z6]),(0,[z1,z2,z349,z7,z4,z5,z6]),(1,[z1,z2,z7,z350,z4,z6]),(0,[z1,z2,z323,z7,z33,z5,z6]),(0,[z351,z1,z2,z7,z4,z5,z6])],[(0,[z81,z1,z2,z32,z7,z4,z6]),(0,[z1,z93,z2,z18,z7,z4,z5]),(0,[z120,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z352,z7,z4,z5,z6]),(1,[z1,z132,z54,z4,z5,z6]),(0,[z1,z2,z75,z7,z4,z5,z152]),(0,[z1,z2,z353,z7,z4,z5,z6])],[(0,[z1,z2,z153,z43,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z17,z6]),(1,[z1,z2,z67,z35,z7,z4])],[(0,[z1,z2,z32,z7,z4,z6,z146]),(0,[z1,z2,z323,z7,z5,z6,z21]),(0,[z1,z2,z35,z7,z12,z4,z6]),(0,[z1,z2,z18,z7,z4,z5,z48]),(0,[z1,z2,z51,z7,z7,z4,z5]),(0,[z1,z2,z9,z7,z4,z5,z6])]],
   [[(0,[z354,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z355,z5,z6]),(0,[z1,z2,z54,z7,z10,z4,z6]),(1,[z1,z2,z18,z33,z4,z5]),(0,[z1,z2,z7,z4,z356,z5,z6]),(1,[z1,z2,z51,z32,z7,z4]),(0,[z1,z2,z357,z7,z4,z6,z78])],[(0,[z1,z2,z75,z7,z4,z5,z146]),(0,[z1,z2,z7,z4,z358,z5,z6]),(0,[z1,z2,z7,z33,z4,z5,z6]),(0,[z89,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z359,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z360,z5,z6]),(0,[z1,z2,z361,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z362,z5,z6]),(0,[z1,z2,z7,z4,z5,z363,z6]),(0,[z1,z2,z7,z364,z4,z5,z6]),(0,[z1,z365,z2,z7,z4,z5,z6]),(0,[z1,z2,z35,z7,z279,z5,z6])],[(0,[z1,z2,z7,z4,z13,z5,z6]),(0,[z1,z2,z7,z4,z366,z5,z6]),(1,[z1,z2,z7,z4,z5,z367]),(0,[z1,z2,z110,z18,z4,z5,z6]),(0,[z1,z2,z7,z368,z4,z5,z6]),(0,[z1,z2,z18,z7,z150,z4,z5]),(0,[z229,z1,z2,z32,z7,z4,z6])],[(0,[z1,z369,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z370,z6]),(0,[z1,z2,z32,z7,z3,z4,z6]),(0,[z1,z2,z7,z371,z4,z5,z6]),(0,[z1,z2,z32,z54,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z372]),(0,[z1,z2,z7,z4,z5,z6,z373]),(0,[z1,z2,z118,z7,z4,z6,z64]),(0,[z1,z2,z7,z258,z5,z6,z64]),(0,[z1,z2,z110,z7,z10,z4,z6]),(1,[z1,z2,z7,z4,z37,z5])],[(0,[z1,z2,z280,z7,z4,z5,z6]),(0,[z1,z2,z82,z51,z7,z4,z5]),(0,[z1,z374,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z199,z13,z6]),(0,[z1,z2,z51,z7,z4,z5,z146]),(0,[z221,z1,z2,z7,z4,z5,z77]),(0,[z1,z2,z7,z4,z5,z375,z6]),(0,[z1,z2,z32,z7,z4,z6,z78])],[(1,[z1,z2,z7,z376,z4,z6]),(0,[z1,z2,z7,z10,z4,z13,z6]),(0,[z1,z72,z2,z7,z17,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z377]),(0,[z1,z2,z217,z7,z4,z5,z6])],[(0,[z378,z1,z2,z7,z4,z5,z6]),(0,[z379,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z10,z4,z6])]],
   [[(0,[z1,z2,z7,z380,z4,z5,z6]),(0,[z1,z2,z381,z7,z4,z5,z6])],[(0,[z1,z382,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z383,z4,z5,z6]),(0,[z1,z2,z7,z43,z10,z4,z6]),(0,[z384,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z385,z5,z6]),(0,[z1,z2,z386,z7,z4,z5,z6]),(0,[z1,z2,z110,z118,z4,z5,z6]),(0,[z1,z2,z18,z7,z4,z5,z6]),(0,[z1,z2,z357,z7,z4,z5,z6]),(0,[z1,z2,z387,z7,z4,z5,z6]),(0,[z1,z2,z67,z79,z4,z5,z6])],[(0,[z1,z2,z7,z4,z388,z5,z6]),(0,[z1,z2,z18,z7,z105,z4,z5]),(0,[z1,z2,z110,z18,z7,z4,z5]),(0,[z1,z2,z7,z12,z4,z39,z6]),(0,[z115,z1,z2,z51,z7,z4,z5])],[(0,[z389,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z4,z5,z6]),(0,[z1,z2,z7,z4,z390,z5,z6]),(1,[z1,z2,z7,z4,z5,z391]),(0,[z1,z392,z2,z7,z4,z5,z6]),(0,[z1,z2,z393,z32,z7,z4,z6]),(0,[z1,z394,z2,z7,z4,z5,z6])],[(0,[z81,z116,z2,z7,z4,z5,z6]),(0,[z1,z54,z7,z43,z4,z5,z6]),(0,[z395,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z396]),(1,[z1,z2,z7,z4,z5,z363]),(0,[z1,z2,z18,z7,z86,z4,z5]),(0,[z397,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z375,z6]),(0,[z1,z2,z398,z7,z4,z5,z6]),(1,[z1,z2,z18,z7,z4,z5])],[(0,[z1,z2,z399,z7,z4,z5,z6]),(0,[z1,z2,z51,z88,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z5,z176]),(0,[z1,z2,z32,z7,z4,z5,z6]),(0,[z1,z2,z400,z7,z4,z5,z6])],[(0,[z1,z2,z401,z7,z4,z5,z6]),(0,[z1,z402,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z403,z6]),(1,[z1,z2,z7,z114,z4,z6])]],
   [[(0,[z1,z404,z2,z7,z4,z5,z6]),(0,[z1,z2,z54,z153,z4,z5,z6]),(0,[z405,z1,z2,z7,z4,z5,z6]),(0,[z50,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z7,z4,z5]),(0,[z1,z2,z406,z18,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z65,z6])],[(0,[z407,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z408,z4,z5,z6])],[(0,[z1,z2,z7,z306,z4,z5,z6]),(0,[z1,z2,z7,z409,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z410,z6]),(0,[z411,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z21]),(0,[z1,z2,z412,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z413,z5,z6])],[(0,[z1,z414,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z415]),(0,[z1,z2,z7,z416,z4,z5,z6]),(0,[z1,z2,z417,z7,z4,z5,z6]),(0,[z1,z2,z418,z7,z4,z5,z6]),(0,[z1,z2,z7,z419,z4,z5,z6])],[(0,[z1,z2,z7,z4,z420,z5,z6]),(0,[z1,z93,z2,z51,z7,z4,z5]),(0,[z1,z2,z18,z7,z4,z5,z146]),(0,[z1,z2,z7,z4,z190,z5,z6]),(0,[z1,z2,z51,z68,z7,z4,z5]),(0,[z1,z2,z32,z7,z4,z5,z122])],[(0,[z1,z2,z7,z4,z5,z6,z421]),(0,[z1,z2,z7,z4,z422,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z423]),(0,[z1,z2,z32,z7,z4,z6,z228]),(0,[z1,z2,z51,z7,z10,z4,z5]),(0,[z1,z2,z424,z7,z4,z5,z6]),(0,[z425,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z75,z7,z4,z426,z6])]],
   [[(0,[z1,z427,z2,z7,z4,z5,z6]),(0,[z1,z428,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z429,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z64]),(1,[z1,z2,z63,z7,z4,z5]),(1,[z1,z2,z110,z18,z4,z5])],[(0,[z1,z2,z430,z7,z4,z5,z6]),(1,[z1,z2,z51,z150,z4,z5]),(0,[z1,z2,z7,z10,z185,z4,z6])],[(0,[z1,z2,z431,z7,z4,z5,z6]),(0,[z1,z2,z75,z7,z4,z5,z77]),(0,[z1,z432,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z41,z1,z2,z7,z10,z4,z6])],[(0,[z1,z2,z7,z4,z5,z6,z137]),(0,[z1,z2,z118,z4,z5,z6,z64]),(0,[z1,z2,z233,z7,z4,z5,z6])],[(0,[z1,z433,z2,z7,z4,z5,z6]),(0,[z1,z2,z18,z434,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z5,z228]),(0,[z1,z2,z67,z7,z4,z39,z6])],[(0,[z1,z2,z51,z7,z4,z5,z77]),(0,[z1,z2,z435,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z330,z6,z21]),(1,[z1,z2,z51,z18,z4,z5]),(0,[z1,z2,z23,z18,z7,z4,z5]),(0,[z1,z2,z32,z7,z177,z4,z6]),(1,[z1,z2,z357,z7,z4,z6])],[(0,[z1,z2,z153,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z436]),(0,[z1,z16,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z10,z4,z141,z6]),(0,[z1,z2,z437,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z438,z5,z6]),(0,[z1,z2,z7,z439,z4,z5,z6]),(0,[z1,z2,z7,z4,z440,z5,z6]),(0,[z1,z2,z441,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z442,z4,z5,z6]),(0,[z1,z2,z443,z7,z4,z5,z6]),(0,[z1,z2,z323,z68,z7,z5,z6]),(0,[z1,z2,z308,z32,z7,z4,z6])],[(0,[z81,z1,z2,z51,z7,z4,z5]),(0,[z444,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z445]),(1,[z1,z2,z267,z7,z4,z5]),(0,[z41,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z446,z7,z4,z5,z6]),(0,[z1,z2,z323,z7,z10,z5,z6])],[(0,[z93,z2,z82,z7,z4,z5,z6]),(0,[z116,z1,z93,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z447]),(0,[z1,z2,z7,z4,z5,z6,z367]),(1,[z1,z2,z32,z18,z7,z4]),(0,[z1,z2,z32,z75,z7,z4,z6]),(1,[z1,z2,z7,z4,z448,z6]),(0,[z449,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z32,z7,z4,z108,z6]),(0,[z102,z1,z2,z7,z4,z31,z6]),(0,[z1,z2,z7,z4,z5,z224,z6]),(0,[z1,z2,z51,z7,z4,z13,z5]),(0,[z1,z16,z2,z7,z4,z5,z391]),(0,[z1,z2,z7,z4,z5,z6,z450]),(0,[z1,z2,z7,z4,z5,z6,z451]),(0,[z1,z452,z2,z7,z4,z5,z6]),(0,[z1,z2,z67,z170,z4,z5,z6])],[(0,[z1,z2,z7,z4,z453,z5,z6]),(0,[z321,z1,z2,z32,z7,z4,z6]),(0,[z1,z132,z2,z32,z7,z4,z6]),(0,[z1,z19,z2,z7,z4,z5,z6]),(0,[z1,z454,z2,z7,z4,z5,z6])],[(0,[z81,z1,z2,z280,z4,z5,z6]),(0,[z1,z2,z110,z150,z4,z5,z6])],[(0,[z455,z1,z2,z7,z4,z5,z6]),(0,[z456,z1,z2,z7,z4,z5,z6]),(1,[z103,z2,z7,z4,z13,z6]),(0,[z1,z2,z457,z7,z4,z5,z6]),(0,[z1,z19,z2,z7,z4,z5,z97]),(0,[z44,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z458,z4,z5,z6]),(1,[z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z35,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z224,z141,z6])]],
   [[(0,[z1,z2,z459,z7,z4,z5,z6]),(0,[z1,z460,z2,z7,z4,z5,z6]),(0,[z461,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z462]),(0,[z1,z2,z7,z4,z5,z363,z64]),(0,[z1,z2,z18,z7,z10,z4,z5])],[(0,[z94,z1,z2,z32,z7,z4,z6]),(0,[z1,z2,z9,z7,z10,z5,z6])],[(0,[z1,z2,z7,z4,z312,z5,z6]),(0,[z1,z2,z7,z4,z5,z300,z6]),(0,[z1,z2,z3,z43,z4,z5,z6]),(0,[z42,z1,z132,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z463,z6]),(0,[z1,z2,z7,z4,z5,z152,z78]),(0,[z1,z2,z7,z464,z4,z5,z6]),(0,[z1,z2,z18,z4,z5,z6,z228]),(0,[z1,z2,z7,z24,z4,z5,z6]),(0,[z1,z2,z121,z7,z4,z5,z6]),(0,[z1,z2,z67,z7,z4,z5,z36])],[(1,[z1,z2,z7,z4,z5,z219]),(0,[z465,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z6,z48]),(0,[z1,z2,z466,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z467]),(0,[z1,z2,z7,z105,z108,z5,z6]),(0,[z44,z1,z2,z18,z7,z4,z5]),(1,[z1,z2,z18,z4,z5,z64]),(0,[z1,z159,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z10,z4,z6,z152])],[(0,[z81,z1,z2,z306,z4,z5,z6]),(0,[z1,z55,z2,z7,z10,z4,z6]),(0,[z1,z2,z118,z7,z10,z4,z6]),(0,[z1,z2,z18,z7,z4,z5,z228]),(0,[z115,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z32,z7,z4,z6,z36])],[(0,[z1,z2,z18,z7,z4,z5,z77]),(0,[z468,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z469,z7,z4,z5,z6]),(0,[z85,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z6,z470])]],
   [[(0,[z1,z2,z7,z4,z5,z471,z6]),(0,[z1,z472,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z17,z6]),(0,[z1,z473,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z474]),(0,[z1,z475,z2,z7,z4,z5,z6])],[(0,[z81,z1,z2,z7,z4,z312,z6]),(0,[z1,z2,z7,z66,z4,z5,z6]),(0,[z476,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z477])],[(0,[z1,z2,z7,z478,z4,z5,z6]),(0,[z1,z479,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z480,z5,z6])],[(0,[z42,z1,z2,z43,z4,z5,z6]),(0,[z1,z56,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z481]),(0,[z1,z2,z253,z7,z33,z4,z5])],[(0,[z94,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z7,z482,z4,z5,z6]),(0,[z1,z2,z18,z7,z4,z13,z5]),(0,[z1,z2,z483,z7,z4,z5,z6]),(0,[z1,z55,z2,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z484,z6]),(0,[z1,z2,z118,z18,z7,z4,z5]),(0,[z115,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z5,z36]),(0,[z485,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z230]),(0,[z486,z1,z2,z7,z4,z5,z6]),(0,[z1,z16,z7,z4,z17,z5,z6]),(0,[z487,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z73,z7,z4,z6,z21]),(0,[z1,z2,z51,z7,z33,z4,z5])],[(0,[z1,z2,z7,z488,z4,z5,z6]),(0,[z50,z1,z2,z7,z4,z5,z77]),(0,[z1,z2,z489,z7,z4,z5,z6]),(0,[z490,z1,z2,z7,z4,z5,z6]),(0,[z491,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z119,z7,z4,z5,z6])],[(0,[z1,z2,z492,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z493]),(0,[z1,z2,z7,z494,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z176,z6]),(0,[z1,z2,z7,z10,z4,z6,z78]),(0,[z1,z2,z32,z68,z7,z5,z6]),(0,[z1,z2,z75,z7,z4,z5,z6]),(0,[z495,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z496,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z497,z7,z4,z5,z6]),(0,[z102,z1,z2,z7,z60,z5,z6]),(0,[z1,z2,z7,z498,z4,z5,z6]),(0,[z1,z499,z2,z7,z4,z5,z6]),(0,[z1,z2,z75,z7,z4,z5,z97]),(0,[z1,z2,z253,z7,z4,z5,z6]),(0,[z1,z2,z7,z500,z4,z5,z6]),(0,[z1,z2,z7,z501,z4,z5,z6])],[(0,[z1,z2,z7,z502,z4,z5,z6]),(0,[z41,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z7,z503,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z504]),(0,[z1,z505,z2,z7,z4,z5,z6]),(0,[z98,z1,z2,z7,z4,z5,z6]),(0,[z506,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z494,z4,z5]),(0,[z1,z507,z2,z7,z4,z5,z6]),(0,[z1,z2,z75,z7,z86,z4,z5])],[(0,[z1,z2,z7,z508,z4,z5,z6]),(0,[z94,z1,z2,z7,z4,z70,z6]),(0,[z1,z2,z183,z7,z4,z5,z6])],[(0,[z1,z2,z7,z105,z4,z5,z6]),(0,[z1,z72,z7,z105,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z97,z6]),(0,[z1,z2,z150,z4,z5,z6,z228]),(0,[z1,z2,z509,z7,z4,z5,z6])],[(0,[z1,z2,z7,z117,z4,z17,z6]),(0,[z1,z2,z51,z7,z4,z5,z97]),(0,[z1,z2,z7,z4,z5,z20,z6]),(0,[z155,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z32,z32,z7,z4,z6]),(0,[z1,z2,z32,z7,z4,z6,z122])],[(0,[z94,z1,z2,z153,z4,z5,z6])],[(0,[z50,z1,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z510]),(0,[z1,z2,z511,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z512,z5,z6])]],
   [[(0,[z513,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z5,z141]),(0,[z1,z2,z7,z10,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z514]),(0,[z1,z515,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z516]),(0,[z1,z2,z7,z517,z4,z5,z6]),(0,[z1,z2,z518,z7,z4,z5,z6])],[(0,[z1,z2,z2,z7,z4,z5,z6]),(0,[z1,z2,z246,z7,z4,z5,z6]),(0,[z1,z72,z2,z7,z4,z5,z6]),(0,[z1,z2,z519,z7,z4,z5,z6]),(1,[z1,z2,z18,z7,z10,z4])],[(0,[z1,z2,z88,z323,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z520]),(0,[z521,z1,z2,z7,z4,z5,z6]),(0,[z1,z522,z2,z7,z4,z5,z6])],[(0,[z1,z2,z523,z7,z4,z5,z6]),(0,[z1,z524,z2,z7,z4,z5,z6]),(0,[z1,z2,z525,z7,z4,z5,z6]),(0,[z1,z2,z7,z114,z4,z5,z6])],[(0,[z81,z1,z2,z7,z10,z4,z6]),(1,[z321,z2,z7,z4,z224,z6]),(0,[z1,z526,z2,z7,z4,z5,z6]),(0,[z44,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z527]),(0,[z1,z2,z323,z33,z4,z5,z6]),(0,[z1,z2,z18,z7,z4,z5,z36]),(0,[z1,z2,z7,z4,z528,z5,z6])],[(0,[z1,z2,z529,z7,z4,z5,z6]),(0,[z1,z2,z530,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z146,z152]),(0,[z1,z2,z7,z531,z4,z5,z6]),(0,[z1,z2,z18,z7,z33,z4,z5]),(0,[z1,z2,z245,z7,z4,z5,z6])],[(0,[z532,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z533,z4,z5,z6]),(0,[z534,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z248,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z535]),(0,[z1,z2,z536,z7,z4,z5,z6]),(0,[z1,z2,z68,z18,z7,z4,z5]),(0,[z1,z2,z209,z7,z10,z4,z6])],[(0,[z1,z2,z32,z7,z60,z4,z6]),(0,[z1,z2,z537,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z213,z6]),(0,[z1,z2,z32,z7,z4,z199,z6]),(0,[z1,z538,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z6,z228]),(0,[z1,z2,z32,z381,z7,z4,z6])],[(0,[z1,z2,z539,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z219]),(0,[z540,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z175,z7,z4,z5,z6])],[(0,[z81,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z541,z6]),(0,[z1,z2,z7,z4,z5,z6,z542]),(0,[z102,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z543,z6]),(1,[z1,z19,z7,z4,z5,z152]),(0,[z1,z2,z262,z7,z4,z5,z6]),(0,[z1,z2,z7,z150,z4,z5,z6]),(0,[z1,z2,z544,z7,z4,z5,z6])],[(0,[z545,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z368,z4,z5])],[(0,[z1,z546,z2,z7,z4,z5,z6]),(0,[z94,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z547,z7,z4,z5,z6]),(0,[z321,z1,z2,z7,z4,z224,z6]),(0,[z1,z2,z248,z7,z4,z5,z6]),(0,[z1,z2,z7,z117,z4,z5,z6]),(0,[z1,z2,z7,z548,z4,z5,z6]),(0,[z1,z55,z2,z51,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z549,z6]),(0,[z1,z2,z88,z7,z4,z5,z6]),(0,[z1,z2,z550,z7,z4,z5,z6])],[(0,[z1,z2,z551,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z326]),(0,[z42,z1,z2,z7,z4,z190,z6]),(0,[z1,z72,z2,z7,z105,z5,z6]),(0,[z1,z2,z18,z7,z4,z5,z97]),(0,[z552,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z553]),(0,[z1,z2,z7,z86,z4,z5,z6])]],
   [[(0,[z554,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z13,z6,z64]),(0,[z1,z2,z555,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z146,z78]),(0,[z556,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z9,z7,z86,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z557])],[(0,[z1,z2,z7,z4,z5,z6,z558]),(0,[z50,z2,z7,z4,z5,z6,z146]),(0,[z221,z1,z2,z32,z7,z4,z6]),(1,[z1,z2,z7,z4,z213,z6]),(0,[z1,z2,z18,z7,z4,z5,z141]),(0,[z1,z2,z7,z559,z4,z5,z6])],[(0,[z1,z2,z7,z4,z560,z5,z6]),(0,[z1,z2,z7,z561,z4,z5,z6]),(0,[z221,z2,z7,z4,z5,z77,z6]),(0,[z1,z2,z7,z562,z4,z5,z6]),(0,[z1,z2,z88,z7,z33,z5,z6])],[(0,[z563,z1,z2,z7,z4,z5,z6]),(0,[z1,z19,z2,z32,z7,z4,z6]),(0,[z1,z2,z84,z7,z4,z5,z21]),(0,[z1,z2,z7,z4,z5,z6,z564]),(0,[z1,z2,z113,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z39,z5,z78])],[(0,[z42,z1,z2,z7,z4,z5,z6]),(0,[z565,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z133]),(0,[z1,z2,z7,z566,z4,z5,z6]),(0,[z1,z187,z2,z7,z4,z5,z6]),(0,[z567,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z332]),(0,[z1,z2,z7,z10,z4,z108,z6]),(0,[z1,z2,z7,z568,z4,z5,z6]),(0,[z569,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z570]),(0,[z1,z2,z88,z7,z5,z6,z21]),(0,[z1,z2,z240,z18,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z326,z6]),(0,[z1,z2,z7,z4,z5,z6,z571])],[(0,[z103,z321,z2,z7,z4,z5,z6]),(0,[z1,z572,z2,z7,z4,z5,z6]),(0,[z1,z2,z18,z33,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z440,z5]),(0,[z1,z2,z195,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z573,z4,z5,z6]),(0,[z1,z2,z574,z7,z4,z5,z6]),(0,[z1,z2,z575,z7,z4,z5,z6]),(0,[z1,z56,z7,z4,z5,z141,z6]),(1,[z1,z2,z7,z4,z5,z34])],[(0,[z94,z1,z2,z7,z4,z300,z6]),(0,[z1,z2,z576,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z577,z5,z6]),(0,[z1,z2,z7,z12,z4,z199,z6]),(1,[z1,z2,z118,z4,z6,z64]),(0,[z1,z2,z7,z4,z5,z6,z578])],[(0,[z81,z1,z2,z7,z508,z5,z6]),(0,[z579,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z466,z32,z7,z4,z6])],[(0,[z1,z2,z7,z4,z580,z5,z6]),(0,[z1,z2,z581,z7,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z6,z64]),(1,[z1,z2,z51,z7,z10,z4]),(0,[z1,z2,z32,z7,z4,z4,z6])],[(0,[z221,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z582,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z5,z21])],[(0,[z1,z2,z7,z4,z5,z6,z583]),(0,[z1,z584,z2,z7,z4,z5,z6]),(0,[z585,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z6,z47]),(0,[z1,z2,z7,z10,z4,z6,z48])],[(0,[z586,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z587,z7,z4,z5,z6]),(0,[z588,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z589]),(0,[z1,z2,z7,z590,z4,z5,z6])],[(0,[z591,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z508,z5,z6]),(0,[z1,z2,z592,z7,z4,z5,z6]),(0,[z1,z2,z324,z7,z4,z5,z6]),(1,[z1,z56,z7,z4,z141,z6]),(0,[z1,z475,z2,z32,z7,z4,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z6,z593]),(0,[z1,z2,z32,z7,z150,z4,z6]),(0,[z1,z2,z67,z32,z7,z4,z6])],[(0,[z1,z2,z7,z594,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z595,z6]),(0,[z1,z2,z51,z7,z4,z5,z64])],[(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z596]),(0,[z1,z2,z597,z7,z4,z5,z6]),(0,[z1,z2,z598,z7,z4,z5,z6]),(0,[z1,z56,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z599])],[(0,[z600,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z601,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z166]),(0,[z1,z2,z7,z10,z4,z77,z6]),(0,[z1,z602,z2,z7,z4,z5,z6]),(0,[z1,z2,z323,z7,z350,z4,z6]),(0,[z1,z2,z32,z323,z7,z4,z6])],[(0,[z116,z1,z2,z7,z4,z5,z6]),(0,[z603,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z376,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z181]),(0,[z1,z2,z293,z7,z10,z4,z6]),(0,[z1,z2,z7,z294,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z604])],[(0,[z2,z153,z7,z3,z4,z5,z6]),(0,[z197,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z7,z605,z4,z5,z6])],[(0,[z1,z606,z2,z7,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z224,z6]),(0,[z1,z2,z7,z607,z4,z5,z6]),(0,[z44,z1,z7,z4,z5,z97,z6]),(0,[z1,z2,z110,z7,z12,z4,z6])],[(0,[z0,z1,z2,z32,z7,z4,z6]),(0,[z41,z2,z7,z4,z108,z5,z6]),(0,[z1,z2,z608,z7,z4,z5,z6]),(0,[z1,z2,z32,z7,z105,z4,z6]),(0,[z1,z2,z7,z4,z5,z141,z6]),(0,[z1,z609,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z156])]],
   [[(1,[z1,z2,z7,z4,z31,z6]),(0,[z1,z2,z7,z4,z5,z426,z6])],[(0,[z116,z93,z2,z7,z4,z5,z6]),(0,[z41,z1,z2,z7,z4,z5,z332]),(0,[z311,z1,z2,z7,z10,z4,z6]),(0,[z610,z1,z2,z7,z4,z5,z6])],[(1,[z50,z2,z7,z4,z5,z146]),(0,[z1,z2,z611,z7,z4,z5,z6]),(0,[z1,z2,z612,z7,z4,z5,z6]),(0,[z1,z2,z51,z32,z7,z4,z6])],[(0,[z1,z2,z613,z7,z4,z5,z6]),(0,[z1,z614,z2,z7,z4,z5,z6]),(0,[z1,z2,z67,z18,z7,z4,z5]),(0,[z1,z2,z7,z615,z4,z5,z6]),(0,[z1,z2,z9,z68,z7,z5,z6])],[(0,[z616,z1,z2,z7,z4,z5,z6]),(0,[z321,z1,z2,z7,z10,z4,z6]),(0,[z103,z1,z2,z32,z7,z4,z6]),(0,[z1,z132,z2,z7,z10,z4,z6]),(0,[z1,z16,z2,z7,z17,z5,z6]),(0,[z1,z2,z617,z7,z4,z5,z6]),(1,[z1,z2,z32,z7,z10,z6]),(1,[z1,z2,z7,z279,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z391]),(0,[z1,z2,z7,z618,z4,z5,z6]),(0,[z1,z2,z18,z7,z4,z5,z21])],[(1,[z1,z2,z619,z7,z4,z6]),(0,[z1,z56,z2,z7,z4,z199,z6]),(0,[z1,z2,z7,z10,z4,z97,z6]),(0,[z1,z2,z323,z7,z10,z4,z6]),(0,[z1,z2,z18,z4,z5,z6,z64]),(1,[z1,z2,z7,z86,z5,z78]),(0,[z1,z2,z7,z4,z317,z5,z6])],[(0,[z1,z2,z82,z7,z4,z5,z6]),(0,[z1,z2,z7,z620,z4,z5,z6]),(0,[z1,z2,z621,z7,z4,z5,z6]),(1,[z1,z2,z119,z7,z4,z5]),(0,[z1,z2,z7,z10,z4,z39,z6])]],
   [[(0,[z1,z622,z2,z7,z4,z5,z6]),(0,[z94,z0,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z623,z4,z5,z6]),(0,[z1,z2,z7,z624,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z625]),(1,[z1,z2,z7,z4,z426,z6])],[(0,[z94,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z626,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z77,z152]),(0,[z1,z72,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z350,z4,z5,z6]),(0,[z1,z2,z9,z32,z7,z4,z6]),(0,[z1,z2,z7,z4,z627,z5,z6])],[(0,[z321,z1,z2,z18,z7,z4,z5]),(0,[z1,z132,z2,z18,z7,z4,z5]),(0,[z1,z2,z18,z7,z4,z5,z64]),(0,[z628,z1,z2,z7,z4,z5,z6])],[(0,[z81,z1,z2,z7,z4,z5,z230]),(0,[z1,z2,z35,z7,z4,z6,z64])],[(0,[z1,z2,z7,z10,z4,z6,z146]),(0,[z1,z2,z323,z7,z4,z375,z6]),(0,[z1,z2,z323,z18,z7,z4,z5]),(0,[z1,z2,z7,z33,z4,z5,z367]),(0,[z1,z2,z74,z7,z5,z6,z64])],[(0,[z221,z1,z2,z51,z7,z4,z5]),(0,[z44,z1,z2,z7,z4,z5,z152]),(0,[z1,z2,z7,z4,z5,z6,z152]),(0,[z1,z2,z7,z4,z5,z6,z629]),(0,[z1,z2,z51,z18,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z65,z5])],[(0,[z1,z2,z7,z4,z5,z6,z630]),(0,[z1,z2,z7,z12,z4,z224,z6]),(0,[z1,z2,z88,z68,z7,z5,z6]),(0,[z334,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z335,z18,z7,z4,z5]),(0,[z1,z2,z7,z10,z408,z4,z6])],[(0,[z41,z1,z2,z7,z4,z5,z166]),(0,[z103,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z631]),(0,[z1,z2,z632,z7,z4,z5,z6]),(0,[z1,z2,z88,z7,z10,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z633]),(0,[z1,z2,z7,z4,z5,z6,z34]),(0,[z1,z2,z7,z4,z5,z6,z470]),(0,[z1,z2,z7,z4,z448,z6,z78])]],
   [[(0,[z321,z1,z2,z7,z4,z13,z6]),(0,[z1,z2,z7,z33,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z634,z6]),(0,[z58,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z376,z4,z108,z6]),(0,[z1,z2,z7,z635,z4,z5,z6]),(0,[z1,z2,z619,z7,z4,z17,z6]),(0,[z1,z2,z290,z7,z4,z5,z6]),(0,[z1,z2,z636,z7,z4,z5,z6]),(0,[z637,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z7,z12,z4,z5]),(1,[z1,z2,z32,z7,z4,z37]),(0,[z1,z638,z2,z7,z4,z5,z6])],[(1,[z1,z2,z333,z7,z4,z5]),(0,[z102,z1,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z639,z4,z5,z6])],[(0,[z1,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z60,z4,z6]),(0,[z1,z2,z7,z4,z5,z77,z78]),(0,[z1,z2,z7,z4,z5,z6,z640]),(0,[z1,z2,z7,z10,z4,z199,z6]),(0,[z1,z2,z7,z641,z4,z5,z6]),(0,[z1,z2,z51,z118,z7,z4,z5])],[(1,[z1,z2,z7,z136,z5,z6]),(0,[z1,z2,z32,z88,z7,z4,z6]),(0,[z1,z2,z9,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z39,z5,z36]),(0,[z1,z2,z642,z7,z4,z5,z6])],[(0,[z643,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z644,z4,z5,z6]),(0,[z1,z2,z7,z645,z4,z5,z6]),(0,[z1,z2,z434,z7,z4,z5,z6])],[(0,[z102,z1,z2,z7,z108,z5,z6]),(0,[z1,z2,z7,z4,z5,z133,z6]),(0,[z1,z2,z646,z7,z4,z5,z6]),(0,[z1,z2,z67,z35,z7,z4,z5])],[(0,[z1,z2,z7,z647,z4,z5,z6]),(0,[z1,z132,z54,z7,z4,z5,z6]),(1,[z1,z2,z217,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z78])]],
   [[(0,[z1,z93,z2,z7,z4,z5,z6]),(0,[z1,z2,z150,z4,z5,z6,z64]),(0,[z1,z2,z7,z4,z448,z5,z6]),(0,[z1,z2,z7,z648,z4,z5,z6])],[(0,[z1,z2,z267,z7,z3,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z649]),(0,[z1,z2,z7,z4,z650,z5,z6]),(0,[z651,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z337,z4,z5,z6]),(0,[z1,z2,z7,z4,z199,z5,z6]),(0,[z1,z2,z7,z652,z4,z5,z6]),(0,[z1,z2,z63,z7,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z37,z5]),(0,[z1,z2,z68,z7,z5,z6,z78])],[(0,[z1,z2,z18,z7,z4,z108,z5]),(0,[z1,z2,z7,z4,z653,z5,z6]),(0,[z42,z1,z2,z32,z7,z4,z6]),(0,[z1,z654,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z181]),(0,[z1,z2,z7,z655,z4,z5,z6]),(0,[z1,z2,z51,z194,z7,z4,z5]),(0,[z656,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z657,z4,z5,z6]),(0,[z1,z2,z7,z4,z39,z5,z6])],[(0,[z1,z2,z51,z7,z43,z4,z5]),(0,[z1,z2,z183,z7,z43,z4,z5]),(1,[z1,z2,z7,z4,z241,z6]),(0,[z237,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z67,z51,z7,z4,z5]),(0,[z1,z2,z32,z68,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z658,z6]),(0,[z1,z2,z33,z4,z5,z6,z21]),(0,[z1,z2,z7,z659,z4,z5,z6]),(0,[z1,z2,z32,z7,z10,z4,z6]),(0,[z1,z2,z68,z7,z10,z4,z6])],[(0,[z1,z2,z51,z153,z7,z4,z5]),(0,[z660,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z661,z5,z6]),(0,[z1,z56,z2,z51,z7,z4,z5]),(0,[z1,z2,z662,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z97,z78]),(1,[z1,z2,z74,z7,z5,z6]),(0,[z1,z2,z18,z18,z7,z4,z5])],[(0,[z50,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z141,z6,z64])]],
   [[(0,[z1,z2,z7,z4,z5,z5,z6]),(0,[z1,z2,z663,z7,z4,z5,z6]),(0,[z1,z2,z51,z110,z7,z4,z5]),(0,[z1,z392,z2,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z664]),(0,[z1,z2,z51,z35,z7,z4,z5]),(0,[z1,z2,z665,z7,z4,z5,z6]),(0,[z1,z2,z75,z7,z4,z39,z5])],[(0,[z1,z2,z7,z108,z17,z5,z6]),(0,[z1,z2,z7,z4,z269,z5,z6]),(0,[z1,z2,z666,z7,z4,z5,z6]),(0,[z1,z2,z54,z7,z4,z5,z6]),(0,[z1,z2,z619,z7,z4,z5,z6]),(0,[z1,z2,z667,z7,z4,z5,z6]),(0,[z1,z2,z35,z7,z4,z6,z36]),(0,[z1,z2,z35,z7,z317,z5,z6])],[(0,[z1,z2,z668,z7,z4,z5,z6]),(0,[z1,z2,z669,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z12,z4,z5])],[(0,[z321,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z7,z4,z670,z5,z6]),(0,[z1,z671,z2,z7,z4,z5,z6]),(0,[z1,z132,z2,z51,z7,z4,z5]),(1,[z1,z2,z323,z33,z5,z6]),(0,[z672,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z399,z18,z7,z4,z5]),(0,[z1,z2,z32,z18,z7,z4,z5]),(0,[z1,z2,z7,z4,z673,z5,z6])],[(0,[z1,z2,z7,z4,z5,z674,z6]),(0,[z1,z2,z7,z4,z5,z6,z675]),(0,[z1,z132,z2,z54,z4,z5,z6]),(1,[z1,z2,z73,z7,z4,z6]),(0,[z1,z2,z676,z7,z4,z5,z6]),(0,[z1,z2,z7,z677,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z39,z5])],[(1,[z0,z2,z153,z4,z5,z6]),(0,[z50,z1,z2,z18,z7,z4,z5]),(0,[z1,z2,z678,z7,z4,z5,z6]),(0,[z1,z679,z2,z7,z4,z5,z6]),(0,[z680,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z110,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z6,z64]),(0,[z586,z1,z2,z32,z7,z4,z6])],[(0,[z1,z2,z7,z681,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z283]),(0,[z1,z2,z51,z51,z7,z4,z5])],[]],
   [[(1,[z1,z2,z7,z4,z5,z6]),(0,[z103,z1,z2,z51,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z17,z5]),(0,[z1,z2,z118,z7,z12,z4,z6])],[(0,[z116,z1,z82,z7,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z13,z6])],[(0,[z1,z2,z7,z4,z5,z6,z682]),(0,[z1,z2,z683,z7,z4,z5,z6]),(0,[z1,z2,z7,z3,z10,z4,z6]),(0,[z41,z1,z2,z7,z60,z5,z6]),(0,[z1,z2,z7,z43,z4,z5,z6]),(1,[z1,z2,z323,z7,z10,z6]),(0,[z1,z2,z7,z336,z4,z5,z6])],[(0,[z116,z1,z2,z32,z7,z4,z6]),(0,[z1,z2,z684,z7,z4,z5,z6]),(0,[z1,z2,z685,z7,z4,z5,z6]),(0,[z1,z2,z406,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z330,z5,z6])],[(1,[z1,z2,z51,z7,z4,z176])],[(0,[z103,z1,z2,z7,z4,z224,z6]),(0,[z1,z2,z7,z4,z224,z6,z64]),(0,[z1,z2,z7,z4,z686,z5,z6]),(0,[z1,z2,z687,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z43,z4,z5]),(0,[z1,z688,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z12,z10,z4,z6]),(0,[z1,z2,z9,z51,z7,z4,z5])],[(0,[z1,z2,z51,z7,z3,z4,z5]),(0,[z1,z2,z153,z7,z10,z4,z6]),(0,[z1,z2,z51,z54,z7,z4,z5]),(0,[z1,z72,z2,z7,z4,z251,z6]),(0,[z1,z55,z2,z7,z4,z141,z6]),(0,[z521,z1,z2,z51,z7,z4,z5])],[(0,[z1,z2,z333,z7,z3,z4,z5]),(0,[z1,z2,z18,z153,z7,z4,z5]),(1,[z102,z2,z7,z60,z5,z6]),(0,[z1,z689,z2,z7,z4,z5,z6]),(0,[z690,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z691,z7,z4,z5,z6]),(1,[z1,z2,z160,z7,z4,z6]),(0,[z2,z7,z4,z5,z77,z6,z146]),(1,[z1,z2,z7,z4,z5,z122])],[(0,[z1,z2,z692,z7,z4,z5,z6]),(0,[z1,z2,z393,z7,z4,z5,z6]),(0,[z221,z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z32,z7,z4,z6,z21]),(0,[z1,z2,z693,z7,z4,z5,z6]),(0,[z1,z2,z694,z7,z4,z5,z6])],[(0,[z695,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z696,z4,z5,z6]),(0,[z94,z2,z7,z3,z4,z5,z6]),(0,[z1,z19,z7,z4,z5,z6,z152])],[(0,[z697,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z698,z6]),(0,[z1,z2,z7,z4,z5,z6,z699]),(0,[z1,z2,z7,z700,z4,z5,z6]),(0,[z1,z19,z2,z7,z10,z4,z6]),(1,[z44,z1,z7,z4,z5,z97])],[(0,[z1,z2,z7,z4,z5,z701,z6]),(0,[z1,z702,z2,z7,z4,z5,z6]),(0,[z703,z1,z2,z7,z4,z5,z6])],[(0,[z321,z2,z7,z4,z5,z224,z6]),(0,[z1,z2,z18,z7,z4,z39,z5]),(0,[z1,z2,z35,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z704]),(0,[z1,z2,z705,z7,z4,z5,z6]),(0,[z1,z2,z79,z7,z4,z5,z6])],[(0,[z1,z2,z82,z32,z7,z4,z6]),(0,[z102,z1,z2,z7,z4,z269,z6]),(1,[z1,z2,z88,z18,z4,z5])],[(0,[z706,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z20])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z7,z4,z5,z707]),(0,[z1,z2,z708,z7,z4,z6]),(0,[z1,z2,z7,z709,z4,z6]),(0,[z1,z2,z18,z4,z5,z367]),(0,[z1,z2,z32,z7,z258,z6]),(0,[z1,z2,z7,z10,z172,z6]),(0,[z1,z2,z32,z7,z4,z37])],[(0,[z1,z2,z7,z4,z5,z710]),(0,[z1,z2,z333,z7,z4,z5]),(0,[z1,z2,z7,z4,z711,z6]),(0,[z1,z19,z32,z7,z4,z152]),(0,[z1,z2,z7,z10,z4,z367]),(0,[z1,z2,z51,z7,z712,z5])],[(0,[z1,z2,z7,z508,z80,z6]),(0,[z1,z2,z14,z7,z10,z6]),(0,[z1,z2,z18,z258,z5,z64]),(0,[z1,z2,z18,z7,z4,z176]),(0,[z1,z2,z7,z4,z65,z176]),(1,[z1,z2,z713,z4,z5])],[(0,[z1,z2,z306,z508,z5,z6]),(0,[z1,z2,z714,z280,z4,z5]),(0,[z1,z2,z323,z7,z715,z6]),(0,[z1,z2,z7,z716,z4,z6])],[(0,[z1,z2,z32,z7,z4,z326]),(0,[z1,z717,z7,z4,z5,z6]),(0,[z1,z2,z718,z7,z4,z6]),(0,[z1,z2,z282,z12,z4,z6]),(0,[z1,z2,z7,z10,z6,z283]),(0,[z1,z2,z7,z86,z5,z283]),(0,[z1,z2,z719,z7,z4,z6]),(0,[z1,z2,z7,z10,z4,z720])],[(0,[z1,z2,z721,z7,z4,z5]),(0,[z1,z2,z7,z722,z5,z6]),(0,[z1,z2,z723,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z724]),(0,[z1,z132,z54,z4,z5,z133]),(0,[z1,z2,z110,z18,z12,z4]),(0,[z1,z2,z7,z10,z4,z37]),(0,[z1,z2,z725,z7,z10,z6])],[(0,[z1,z2,z7,z508,z312,z6]),(0,[z1,z2,z7,z4,z5,z726]),(0,[z42,z1,z248,z43,z4,z5]),(0,[z1,z2,z18,z7,z4,z251]),(0,[z1,z2,z7,z10,z5,z122])],[(0,[z1,z2,z7,z4,z727,z6]),(0,[z1,z2,z7,z4,z728,z6]),(0,[z1,z2,z7,z4,z5,z729]),(0,[z1,z2,z73,z88,z6,z21]),(0,[z1,z2,z730,z7,z4,z375]),(0,[z1,z2,z74,z7,z10,z6]),(1,[z1,z2,z18,z4,z176]),(0,[z1,z2,z731,z18,z7,z4]),(0,[z1,z2,z35,z7,z4,z122])]],
   [[(0,[z1,z2,z732,z7,z4,z6]),(0,[z680,z1,z2,z7,z10,z6]),(0,[z1,z2,z357,z18,z7,z4])],[(0,[z1,z733,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z391]),(0,[z1,z2,z170,z4,z5,z6]),(0,[z1,z2,z7,z4,z37,z64]),(0,[z1,z2,z694,z7,z10,z6])],[(0,[z1,z2,z734,z7,z4,z5]),(0,[z1,z2,z18,z655,z4,z5]),(0,[z1,z2,z7,z10,z4,z363]),(0,[z1,z2,z32,z7,z4,z735]),(0,[z1,z46,z2,z113,z4,z6])],[(0,[z1,z2,z7,z736,z5,z6]),(0,[z1,z2,z7,z737,z4,z6]),(0,[z1,z2,z32,z7,z4,z332]),(0,[z1,z2,z18,z4,z224,z64]),(0,[z1,z2,z7,z738,z4,z6]),(0,[z1,z2,z725,z7,z5,z6]),(0,[z1,z2,z32,z7,z605,z6]),(0,[z1,z2,z7,z4,z39,z122])],[(0,[z1,z2,z7,z739,z5,z6]),(0,[z94,z2,z333,z3,z4,z5]),(0,[z1,z2,z323,z33,z10,z6]),(0,[z1,z740,z18,z7,z4,z5]),(0,[z1,z2,z18,z657,z4,z5])],[(0,[z1,z132,z51,z54,z4,z5]),(0,[z1,z2,z74,z7,z5,z6]),(0,[z1,z2,z63,z7,z4,z176])],[(0,[z1,z2,z741,z7,z4,z5]),(0,[z0,z2,z32,z153,z4,z6]),(0,[z461,z2,z153,z4,z5,z6]),(0,[z102,z2,z7,z742,z5,z6]),(0,[z1,z2,z32,z7,z4,z34]),(0,[z1,z2,z743,z32,z7,z4]),(0,[z1,z2,z51,z150,z4,z176]),(0,[z1,z2,z233,z7,z10,z78])],[(0,[z1,z2,z744,z7,z136,z6]),(0,[z102,z2,z32,z7,z60,z6]),(0,[z1,z2,z7,z10,z4,z133]),(0,[z1,z2,z51,z353,z4,z5]),(0,[z1,z2,z745,z7,z4,z5]),(0,[z1,z2,z323,z253,z33,z5]),(0,[z1,z2,z18,z4,z5,z746]),(0,[z1,z2,z233,z209,z7,z4])]],
   [[(0,[z1,z2,z7,z4,z747,z6]),(0,[z1,z2,z7,z4,z748,z6]),(0,[z1,z2,z749,z4,z6,z64]),(0,[z1,z2,z118,z18,z4,z64]),(1,[z1,z2,z18,z258,z5]),(0,[z1,z2,z750,z7,z4,z6]),(0,[z311,z2,z7,z66,z4,z6])],[(0,[z1,z2,z7,z4,z751,z6]),(0,[z1,z2,z7,z4,z190,z6]),(0,[z1,z2,z7,z4,z752,z6]),(0,[z753,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z754]),(0,[z1,z755,z18,z7,z4,z5]),(0,[z1,z2,z756,z4,z5,z6]),(0,[z1,z2,z32,z757,z7,z4]),(0,[z1,z2,z357,z7,z4,z39])],[(0,[z1,z2,z7,z4,z5,z758]),(0,[z1,z2,z7,z4,z759,z6]),(0,[z1,z2,z323,z33,z5,z6]),(0,[z1,z2,z217,z7,z10,z6]),(0,[z1,z2,z67,z7,z10,z78]),(0,[z1,z2,z32,z713,z7,z4]),(0,[z1,z2,z760,z7,z4,z36])],[(0,[z1,z2,z280,z4,z5,z230]),(0,[z1,z2,z7,z761,z5,z6]),(0,[z1,z2,z762,z7,z4,z6]),(0,[z1,z2,z763,z4,z5,z6]),(0,[z1,z2,z73,z7,z4,z6]),(0,[z1,z2,z7,z4,z176,z6]),(0,[z1,z2,z51,z18,z4,z176]),(0,[z1,z2,z764,z7,z4,z5]),(0,[z1,z2,z92,z10,z6,z78]),(0,[z1,z2,z67,z209,z7,z4]),(0,[z1,z2,z92,z86,z5,z78]),(0,[z1,z2,z7,z279,z6,z36]),(0,[z58,z1,z2,z7,z279,z6])],[(0,[z1,z2,z51,z7,z4,z80]),(0,[z1,z2,z7,z4,z765,z5]),(0,[z0,z2,z153,z4,z5,z6]),(0,[z1,z2,z323,z25,z5,z6])],[(0,[z1,z132,z54,z4,z5,z181]),(0,[z1,z2,z766,z7,z4,z5]),(0,[z1,z2,z619,z18,z7,z4]),(0,[z1,z2,z18,z4,z5,z493]),(0,[z1,z2,z119,z4,z5,z64]),(0,[z1,z2,z32,z68,z7,z6]),(0,[z1,z2,z7,z615,z5,z78])],[(0,[z1,z2,z32,z306,z4,z6]),(0,[z1,z2,z767,z7,z4,z5]),(0,[z1,z2,z7,z4,z768,z5]),(0,[z1,z2,z769,z7,z4,z6]),(0,[z1,z2,z7,z4,z770,z6]),(0,[z1,z2,z51,z771,z7,z5]),(0,[z1,z2,z7,z24,z4,z470])],[(0,[z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z280,z136,z5,z6]),(0,[z1,z2,z7,z4,z772,z6]),(0,[z1,z2,z7,z773,z5,z6]),(0,[z1,z16,z51,z7,z17,z5]),(0,[z1,z2,z88,z18,z10,z4]),(0,[z1,z2,z63,z74,z7,z5]),(0,[z1,z2,z110,z32,z18,z4]),(0,[z1,z2,z262,z51,z7,z10])]],
   [[(0,[z1,z2,z7,z774,z4,z6]),(0,[z1,z2,z775,z7,z4,z5]),(0,[z1,z2,z7,z10,z548,z6]),(0,[z1,z2,z32,z18,z7,z10]),(0,[z1,z2,z51,z92,z4,z5])],[(0,[z1,z2,z32,z7,z4,z166]),(0,[z1,z72,z7,z105,z241,z6]),(0,[z1,z2,z323,z7,z10,z6]),(0,[z1,z2,z7,z776,z4,z5]),(0,[z1,z2,z323,z777,z5,z6]),(0,[z1,z2,z32,z323,z33,z6]),(0,[z1,z2,z7,z10,z494,z6]),(0,[z1,z2,z7,z4,z39,z176]),(0,[z1,z2,z760,z7,z4,z6])],[(0,[z1,z2,z7,z4,z778,z6]),(0,[z1,z2,z779,z7,z4,z5]),(0,[z1,z2,z32,z7,z4,z181]),(0,[z1,z2,z7,z4,z780,z6]),(0,[z1,z2,z18,z566,z4,z5]),(0,[z1,z2,z18,z7,z4,z781])],[(0,[z1,z2,z782,z4,z5,z6]),(0,[z1,z2,z783,z7,z4,z5]),(0,[z41,z2,z7,z108,z5,z6]),(0,[z1,z2,z51,z431,z4,z5]),(0,[z1,z2,z7,z4,z784,z6]),(0,[z1,z2,z7,z785,z5,z6]),(0,[z1,z2,z51,z7,z4,z176]),(0,[z1,z2,z786,z4,z5,z228]),(0,[z58,z1,z2,z7,z10,z6]),(0,[z1,z2,z7,z10,z6,z48]),(0,[z1,z2,z32,z7,z4,z787])],[(0,[z1,z2,z7,z788,z5,z6]),(0,[z1,z2,z7,z4,z789,z5]),(0,[z1,z2,z7,z790,z4,z6]),(0,[z1,z2,z75,z7,z4,z65])],[(0,[z1,z2,z791,z4,z5,z6]),(0,[z303,z2,z7,z4,z224,z6]),(0,[z1,z2,z110,z18,z4,z64]),(0,[z1,z2,z35,z18,z4,z64]),(0,[z1,z2,z51,z32,z18,z4]),(0,[z1,z2,z32,z68,z7,z122])],[(0,[z1,z2,z7,z792,z5,z6]),(0,[z1,z2,z32,z7,z347,z6]),(0,[z1,z2,z18,z7,z4,z793])],[(0,[z1,z2,z7,z136,z80,z6]),(0,[z1,z2,z160,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z794]),(0,[z1,z2,z7,z795,z5,z6]),(0,[z1,z2,z18,z7,z350,z4]),(0,[z1,z2,z7,z4,z5,z122]),(0,[z1,z2,z796,z4,z5,z6]),(0,[z1,z2,z7,z4,z37,z36])]],
   [[(0,[z1,z2,z306,z136,z5,z6]),(0,[z1,z2,z797,z7,z4,z5]),(0,[z50,z2,z32,z7,z4,z146]),(0,[z1,z2,z7,z4,z5,z798]),(0,[z1,z132,z799,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z800]),(0,[z1,z2,z18,z7,z4,z65]),(0,[z1,z2,z32,z18,z4,z228]),(0,[z1,z2,z18,z7,z4,z448])],[(0,[z1,z2,z7,z801,z4,z6]),(0,[z1,z56,z7,z4,z802,z6]),(0,[z1,z2,z18,z7,z4,z330]),(0,[z1,z2,z32,z253,z7,z4])],[(0,[z1,z2,z803,z7,z4,z6]),(0,[z1,z2,z7,z804,z4,z6]),(0,[z103,z2,z381,z7,z4,z6]),(0,[z1,z2,z18,z575,z4,z5]),(0,[z1,z2,z7,z805,z4,z6]),(0,[z1,z2,z73,z7,z4,z20])],[(0,[z1,z2,z7,z136,z312,z6]),(0,[z1,z2,z7,z777,z5,z6])],[(0,[z1,z2,z7,z4,z806,z6]),(0,[z221,z2,z7,z4,z5,z729]),(0,[z1,z2,z51,z7,z258,z5]),(0,[z1,z2,z32,z807,z7,z4])],[(0,[z1,z2,z808,z7,z4,z5]),(0,[z321,z2,z18,z7,z4,z224]),(0,[z491,z2,z7,z4,z224,z6]),(0,[z1,z72,z7,z105,z5,z6]),(0,[z1,z2,z88,z150,z10,z6]),(0,[z1,z2,z84,z7,z10,z4]),(0,[z1,z2,z7,z10,z715,z6])],[(0,[z41,z2,z7,z376,z108,z6]),(0,[z1,z2,z7,z4,z5,z20]),(0,[z1,z2,z51,z7,z4,z809]),(0,[z1,z2,z32,z7,z317,z6]),(0,[z1,z2,z693,z7,z5,z78])],[(0,[z41,z2,z7,z10,z108,z6]),(0,[z1,z2,z7,z4,z5,z810]),(0,[z2,z7,z4,z5,z6,z811]),(0,[z1,z2,z51,z323,z7,z10]),(0,[z1,z2,z7,z4,z812,z6]),(0,[z1,z2,z7,z10,z356,z6]),(0,[z1,z2,z796,z4,z5,z122]),(0,[z1,z2,z813,z7,z5,z78])]],
   [[(0,[z1,z2,z814,z7,z4,z5]),(0,[z1,z2,z815,z7,z4,z6]),(0,[z42,z1,z43,z4,z190,z6]),(0,[z1,z2,z7,z4,z5,z134]),(0,[z1,z2,z7,z4,z251,z6]),(0,[z1,z2,z18,z315,z4,z5]),(0,[z1,z2,z7,z4,z65,z36]),(0,[z58,z1,z2,z7,z4,z37])],[(0,[z1,z2,z7,z4,z816,z6]),(0,[z1,z2,z32,z667,z7,z6]),(0,[z1,z2,z67,z217,z4,z5])],[(0,[z1,z2,z817,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z818]),(1,[z2,z7,z742,z5,z6]),(0,[z1,z2,z819,z4,z5,z6]),(0,[z1,z2,z18,z7,z4,z213]),(0,[z1,z2,z7,z4,z820,z6]),(0,[z1,z2,z7,z821,z4,z6]),(0,[z1,z2,z88,z18,z10,z6]),(0,[z1,z2,z88,z10,z6,z47]),(0,[z1,z2,z18,z10,z4,z64]),(0,[z1,z2,z32,z7,z4,z822])],[(0,[z1,z2,z523,z7,z10,z6]),(0,[z1,z2,z823,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z824]),(0,[z1,z2,z23,z18,z4,z64]),(0,[z1,z2,z74,z18,z5,z64]),(0,[z1,z2,z119,z7,z10,z4]),(0,[z1,z825,z7,z10,z4,z6]),(0,[z1,z2,z7,z10,z325,z6]),(0,[z1,z2,z79,z4,z5,z36])],[(0,[z1,z2,z7,z4,z826,z6]),(0,[z1,z2,z827,z4,z5,z6]),(0,[z1,z2,z7,z828,z4,z6]),(0,[z1,z2,z829,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z830]),(0,[z1,z2,z7,z4,z831,z6]),(0,[z1,z2,z7,z10,z4,z832]),(0,[z1,z46,z2,z7,z4,z37]),(0,[z1,z2,z68,z217,z5,z6])],[(0,[z1,z2,z833,z7,z4,z5]),(0,[z41,z2,z18,z7,z108,z5]),(0,[z1,z2,z18,z4,z5,z553]),(0,[z1,z2,z7,z10,z6,z122]),(0,[z1,z2,z834,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z835]),(0,[z102,z2,z7,z60,z269,z6]),(0,[z1,z2,z7,z4,z836,z6]),(0,[z1,z2,z88,z5,z6,z21]),(0,[z1,z2,z18,z7,z837,z5])],[(0,[z22,z1,z2,z7,z10,z6]),(0,[z1,z2,z118,z258,z6,z64]),(0,[z120,z2,z7,z408,z4,z6])]],
   [[(0,[z1,z2,z838,z4,z5,z6]),(0,[z1,z2,z7,z4,z839,z6]),(0,[z1,z2,z7,z840,z4,z6]),(0,[z1,z2,z7,z4,z5,z841])],[(0,[z495,z2,z7,z4,z5,z146]),(0,[z1,z2,z7,z4,z802,z6]),(0,[z842,z2,z18,z7,z4,z5]),(1,[z1,z2,z760,z7,z4])],[(0,[z1,z2,z843,z7,z4,z6]),(0,[z1,z2,z7,z10,z422,z6]),(0,[z0,z2,z51,z153,z4,z5]),(0,[z1,z2,z844,z7,z4,z5]),(0,[z1,z2,z88,z7,z10,z6]),(0,[z1,z2,z88,z777,z5,z6]),(0,[z1,z2,z18,z7,z4,z375]),(0,[z1,z2,z32,z217,z4,z6]),(0,[z1,z2,z845,z4,z5,z6])],[(0,[z1,z2,z7,z4,z80,z6]),(0,[z81,z82,z7,z4,z5,z6]),(0,[z1,z2,z744,z7,z4,z6]),(0,[z1,z2,z846,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z230]),(0,[z847,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z848,z5,z6]),(0,[z1,z2,z7,z10,z6,z149]),(0,[z1,z2,z118,z4,z363,z64]),(0,[z1,z2,z7,z10,z279,z6])],[(0,[z94,z2,z3,z4,z70,z6]),(0,[z1,z2,z18,z7,z849,z4]),(0,[z1,z2,z743,z7,z4,z5])],[(0,[z2,z7,z4,z5,z6,z850]),(0,[z1,z2,z88,z4,z5,z20]),(0,[z1,z2,z92,z4,z5,z6]),(0,[z1,z2,z74,z18,z7,z5])],[(0,[z1,z2,z333,z7,z10,z4]),(0,[z1,z2,z7,z4,z5,z851]),(0,[z1,z2,z18,z4,z13,z64]),(0,[z1,z7,z4,z5,z852,z6]),(0,[z1,z2,z343,z18,z4,z5]),(0,[z1,z2,z18,z195,z10,z4])],[(0,[z1,z2,z7,z4,z312,z6]),(0,[z1,z2,z7,z853,z4,z6]),(0,[z1,z2,z7,z854,z5,z6]),(0,[z1,z2,z7,z855,z4,z6]),(0,[z2,z7,z4,z5,z77,z729]),(0,[z1,z2,z7,z4,z856,z6]),(0,[z1,z2,z88,z323,z10,z6]),(0,[z1,z2,z857,z7,z4,z6]),(0,[z1,z2,z18,z4,z5,z578]),(0,[z1,z2,z18,z7,z114,z4]),(0,[z1,z2,z7,z317,z5,z6]),(0,[z1,z2,z67,z357,z7,z4])]],
   [[(0,[z1,z2,z7,z4,z858,z6]),(0,[z1,z2,z7,z4,z859,z6]),(0,[z1,z2,z7,z4,z860,z6]),(0,[z1,z2,z51,z7,z350,z4]),(0,[z1,z2,z757,z7,z4,z5]),(0,[z1,z2,z170,z4,z39,z6])],[(0,[z1,z2,z7,z4,z861,z6]),(0,[z862,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z863]),(0,[z1,z16,z7,z17,z5,z134]),(0,[z1,z2,z88,z330,z6,z21]),(0,[z1,z2,z32,z7,z566,z6]),(0,[z1,z2,z51,z7,z4,z65]),(0,[z1,z2,z786,z4,z5,z6]),(0,[z1,z2,z18,z7,z279,z5]),(0,[z1,z2,z51,z7,z4,z448]),(0,[z1,z2,z7,z10,z162,z6])],[(0,[z1,z2,z7,z4,z5,z864]),(0,[z1,z2,z32,z88,z6,z21]),(0,[z1,z2,z51,z7,z4,z330]),(0,[z1,z2,z118,z749,z4,z6]),(0,[z1,z2,z217,z10,z4,z6]),(0,[z1,z2,z67,z7,z279,z6])],[(1,[z2,z865,z4,z5,z6]),(0,[z1,z2,z7,z10,z388,z6]),(0,[z1,z2,z7,z866,z4,z6]),(0,[z1,z2,z7,z4,z5,z867]),(0,[z1,z16,z7,z10,z17,z6]),(0,[z1,z2,z110,z368,z4,z6]),(0,[z1,z2,z7,z4,z868,z6])],[(1,[z2,z7,z4,z5,z729]),(0,[z1,z2,z869,z7,z4,z5])],[(0,[z1,z2,z870,z7,z4,z6]),(0,[z1,z2,z7,z4,z809,z6]),(0,[z229,z2,z7,z4,z224,z6]),(0,[z1,z2,z7,z4,z871,z6]),(0,[z1,z56,z51,z7,z4,z141]),(0,[z1,z2,z7,z4,z872,z5]),(0,[z1,z2,z51,z323,z33,z5]),(0,[z873,z2,z18,z7,z4,z5]),(0,[z1,z2,z874,z7,z10,z4])],[(0,[z1,z2,z18,z7,z4,z80]),(0,[z1,z2,z7,z117,z4,z6])],[(0,[z1,z2,z875,z7,z4,z6]),(0,[z1,z2,z267,z32,z7,z4]),(0,[z1,z2,z7,z876,z4,z6]),(0,[z1,z2,z7,z877,z4,z6]),(0,[z1,z2,z7,z4,z878,z6]),(0,[z1,z2,z32,z68,z18,z7]),(0,[z229,z2,z393,z7,z4,z6]),(0,[z1,z2,z32,z796,z4,z6]),(0,[z1,z2,z7,z4,z39,z36]),(0,[z1,z2,z67,z35,z7,z279])]],
   [[(0,[z1,z2,z7,z879,z4,z6]),(0,[z1,z2,z7,z4,z880,z6]),(0,[z1,z2,z32,z88,z18,z4]),(0,[z1,z2,z7,z279,z6,z64]),(0,[z1,z2,z51,z7,z4,z881])],[(0,[z1,z2,z7,z4,z5,z137]),(0,[z1,z2,z7,z882,z5,z6]),(0,[z1,z132,z54,z4,z5,z6]),(0,[z1,z2,z340,z7,z10,z6]),(0,[z1,z2,z883,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z884]),(1,[z1,z2,z749,z4,z6]),(0,[z1,z2,z110,z12,z4,z34]),(0,[z1,z159,z246,z7,z4,z5]),(0,[z1,z2,z32,z79,z4,z6])],[(0,[z1,z2,z7,z4,z5,z885]),(0,[z1,z2,z544,z4,z6,z64]),(0,[z1,z2,z99,z18,z4,z5]),(0,[z1,z2,z18,z92,z4,z5]),(0,[z1,z2,z760,z7,z4,z39]),(0,[z1,z2,z35,z170,z4,z6])],[(0,[z1,z2,z7,z4,z886,z6]),(0,[z1,z2,z7,z887,z4,z6]),(0,[z1,z2,z51,z7,z4,z213]),(0,[z1,z2,z9,z75,z7,z10])],[(0,[z1,z143,z7,z4,z5,z97]),(0,[z1,z2,z18,z7,z4,z751]),(0,[z1,z2,z51,z32,z7,z4]),(0,[z1,z2,z7,z86,z448,z78])],[(0,[z1,z888,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z889,z6]),(0,[z1,z7,z4,z5,z6,z890]),(0,[z545,z2,z7,z108,z5,z6]),(0,[z891,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z258,z141,z6]),(0,[z1,z2,z7,z4,z892,z6]),(0,[z1,z2,z262,z217,z4,z5])],[(0,[z1,z2,z32,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z893]),(0,[z41,z2,z51,z7,z108,z5]),(0,[z1,z2,z894,z7,z4,z6]),(0,[z1,z2,z18,z249,z4,z5]),(0,[z1,z2,z612,z7,z10,z6]),(0,[z1,z2,z895,z7,z4,z6]),(0,[z1,z2,z7,z4,z896,z6])],[(0,[z1,z2,z18,z280,z4,z5]),(0,[z1,z2,z7,z594,z5,z78]),(0,[z1,z72,z32,z7,z105,z6]),(0,[z1,z2,z7,z4,z5,z367]),(0,[z1,z2,z110,z749,z4,z6]),(0,[z1,z2,z32,z796,z4,z122])]],
   [[(0,[z1,z2,z7,z508,z5,z230]),(0,[z1,z2,z897,z7,z4,z5]),(0,[z44,z1,z52,z7,z4,z5]),(0,[z1,z2,z7,z10,z258,z6]),(0,[z521,z1,z2,z7,z4,z65]),(0,[z1,z2,z7,z4,z37,z5]),(0,[z1,z2,z68,z7,z5,z122]),(0,[z1,z2,z67,z7,z4,z426])],[(0,[z1,z2,z32,z161,z7,z6]),(0,[z1,z2,z898,z7,z4,z5]),(0,[z1,z19,z7,z10,z4,z152])],[(0,[z1,z2,z799,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z899]),(0,[z1,z2,z308,z32,z18,z4]),(0,[z1,z2,z51,z7,z317,z5])],[(0,[z1,z2,z51,z7,z4,z375]),(0,[z1,z2,z18,z336,z4,z5]),(0,[z1,z2,z900,z10,z4,z6])],[(0,[z1,z2,z901,z7,z4,z5]),(0,[z1,z2,z7,z10,z4,z326]),(0,[z1,z2,z9,z18,z7,z10]),(0,[z1,z2,z7,z4,z902,z6]),(0,[z1,z2,z813,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z903])],[(0,[z1,z2,z7,z904,z4,z6]),(0,[z1,z7,z905,z17,z5,z6]),(0,[z1,z2,z906,z7,z4,z5]),(0,[z1,z2,z18,z7,z258,z5]),(0,[z1,z2,z32,z7,z4,z122])],[(0,[z81,z82,z7,z4,z80,z6]),(0,[z1,z2,z7,z4,z907,z6]),(0,[z1,z2,z908,z7,z4,z5]),(0,[z1,z2,z909,z7,z4,z5]),(0,[z1,z2,z7,z4,z910,z6]),(0,[z321,z2,z7,z4,z911,z6]),(0,[z1,z2,z912,z7,z4,z5]),(1,[z1,z2,z51,z7,z712]),(0,[z1,z2,z51,z32,z68,z7]),(0,[z1,z2,z32,z713,z4,z5]),(0,[z1,z2,z67,z7,z4,z37])]],
   [[(0,[z1,z2,z714,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z913]),(0,[z1,z2,z7,z4,z914,z6]),(0,[z1,z2,z7,z4,z915,z6]),(0,[z1,z2,z18,z419,z4,z5]),(0,[z1,z2,z51,z7,z114,z4])],[(0,[z94,z2,z32,z3,z4,z6]),(0,[z1,z2,z183,z7,z4,z5]),(0,[z44,z1,z32,z7,z4,z97]),(0,[z1,z2,z262,z18,z4,z5]),(0,[z1,z2,z88,z18,z5,z21])],[(0,[z1,z2,z916,z4,z5,z6]),(0,[z94,z2,z3,z4,z300,z6]),(0,[z85,z2,z7,z4,z5,z77]),(0,[z1,z2,z7,z917,z4,z6]),(0,[z1,z2,z7,z258,z39,z6]),(0,[z1,z2,z51,z7,z279,z5]),(0,[z1,z2,z357,z7,z10,z6]),(0,[z1,z2,z918,z7,z4,z5])],[(0,[z81,z82,z7,z4,z312,z6]),(0,[z1,z2,z7,z10,z4,z332]),(0,[z1,z7,z4,z5,z97,z852]),(0,[z1,z2,z357,z92,z4,z6])],[(0,[z1,z2,z7,z919,z4,z6]),(0,[z1,z2,z7,z4,z920,z6]),(0,[z1,z2,z7,z4,z5,z921]),(0,[z1,z2,z922,z4,z5,z6])],[(0,[z1,z2,z7,z4,z923,z6]),(0,[z1,z2,z924,z7,z4,z5]),(0,[z1,z2,z32,z7,z4,z20]),(0,[z1,z2,z217,z4,z448,z6])],[(0,[z1,z2,z7,z4,z5,z925]),(0,[z1,z2,z7,z4,z926,z6]),(0,[z1,z2,z7,z10,z6,z260]),(0,[z44,z1,z7,z10,z4,z97]),(0,[z1,z2,z7,z4,z5,z746]),(0,[z1,z2,z7,z10,z4,z34]),(0,[z1,z2,z424,z7,z10,z6]),(0,[z1,z2,z32,z7,z4,z872])],[(0,[z102,z2,z7,z10,z60,z6]),(0,[z1,z2,z7,z4,z927,z6]),(0,[z1,z2,z7,z4,z928,z6]),(0,[z1,z2,z32,z7,z4,z134]),(0,[z1,z2,z217,z4,z39,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z929]),(0,[z1,z2,z7,z4,z70,z6]),(0,[z1,z2,z51,z619,z7,z4]),(0,[z1,z2,z84,z88,z5,z21]),(0,[z1,z2,z725,z7,z4,z6])],[(0,[z1,z2,z930,z4,z5,z6]),(0,[z1,z2,z63,z7,z258,z5]),(1,[z1,z2,z786,z4,z5]),(0,[z1,z2,z51,z7,z712,z6])],[(0,[z1,z2,z7,z853,z508,z6]),(0,[z221,z2,z7,z4,z5,z77]),(0,[z1,z2,z67,z35,z79,z4])],[(0,[z1,z2,z18,z442,z4,z5]),(0,[z1,z2,z931,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z932]),(0,[z1,z2,z7,z837,z5,z6]),(0,[z1,z2,z110,z119,z4,z5])],[(0,[z1,z2,z7,z4,z5,z933]),(0,[z0,z2,z18,z153,z4,z5]),(0,[z1,z2,z110,z18,z4,z5])],[(0,[z1,z2,z7,z4,z80,z137]),(0,[z81,z82,z7,z4,z5,z137]),(0,[z1,z2,z7,z4,z934,z6]),(0,[z102,z2,z18,z7,z60,z5]),(0,[z1,z2,z51,z118,z4,z64]),(0,[z1,z2,z7,z935,z4,z5]),(0,[z1,z2,z51,z150,z4,z5]),(0,[z1,z2,z936,z7,z6,z78])],[(0,[z2,z7,z60,z742,z5,z6]),(0,[z1,z2,z7,z937,z5,z6]),(0,[z1,z2,z777,z5,z6,z21]),(0,[z1,z2,z38,z12,z4,z6])],[(0,[z2,z7,z4,z911,z5,z6]),(0,[z1,z16,z619,z7,z17,z6]),(0,[z85,z2,z399,z7,z4,z5])]],
   [[(0,[z1,z2,z51,z280,z4,z5]),(0,[z1,z2,z7,z4,z5,z938]),(0,[z1,z16,z7,z17,z5,z391]),(0,[z1,z2,z18,z4,z5,z193]),(0,[z1,z2,z18,z7,z761,z5]),(0,[z1,z2,z936,z7,z10,z6])],[(0,[z1,z2,z7,z4,z312,z137]),(0,[z1,z2,z7,z10,z4,z166]),(0,[z1,z2,z18,z7,z4,z31]),(0,[z1,z475,z7,z4,z141,z6])],[(0,[z1,z2,z7,z4,z5,z939]),(0,[z81,z82,z32,z7,z4,z6]),(0,[z42,z1,z43,z10,z4,z6]),(0,[z1,z2,z7,z10,z4,z181]),(0,[z1,z7,z4,z802,z141,z6]),(0,[z1,z2,z940,z7,z4,z5]),(0,[z1,z2,z51,z18,z4,z5])],[(0,[z1,z2,z7,z4,z5,z941]),(0,[z1,z2,z63,z7,z4,z39]),(0,[z1,z2,z51,z7,z4,z892]),(0,[z1,z2,z942,z7,z4,z5])],[(0,[z1,z2,z18,z306,z4,z5]),(0,[z1,z2,z253,z7,z4,z5]),(0,[z1,z2,z32,z18,z4,z64])],[(0,[z1,z2,z7,z136,z5,z230]),(0,[z1,z2,z32,z7,z136,z6]),(0,[z1,z2,z943,z4,z5,z6]),(0,[z1,z2,z267,z7,z4,z5]),(0,[z1,z2,z7,z4,z944,z6]),(0,[z1,z2,z7,z4,z945,z6]),(0,[z1,z2,z92,z4,z5,z367]),(0,[z1,z2,z32,z119,z7,z4]),(0,[z1,z2,z51,z786,z4,z5])],[(0,[z1,z2,z7,z4,z946,z6]),(0,[z1,z2,z7,z4,z947,z6]),(0,[z1,z2,z248,z32,z7,z4]),(0,[z1,z2,z7,z258,z5,z6]),(0,[z1,z2,z7,z4,z448,z6])],[(0,[z2,z153,z865,z4,z5,z6]),(0,[z1,z2,z7,z10,z348,z6]),(0,[z1,z56,z18,z7,z4,z141]),(0,[z1,z2,z7,z948,z4,z6]),(0,[z1,z2,z7,z12,z4,z37]),(0,[z1,z2,z51,z441,z4,z5]),(0,[z1,z2,z9,z209,z7,z10])]],
   [[(0,[z1,z2,z949,z306,z4,z5]),(0,[z1,z2,z7,z950,z4,z6]),(0,[z50,z2,z7,z10,z4,z146]),(0,[z1,z2,z951,z7,z4,z6]),(0,[z1,z2,z51,z501,z4,z5])],[(0,[z1,z2,z32,z7,z508,z6]),(0,[z1,z2,z7,z4,z5,z952]),(0,[z1,z2,z730,z7,z4,z5]),(0,[z1,z2,z7,z10,z127,z6]),(0,[z1,z2,z18,z7,z10,z78]),(0,[z1,z2,z953,z10,z4,z6]),(0,[z1,z2,z7,z10,z6,z316])],[(0,[z1,z2,z51,z7,z4,z5]),(0,[z94,z2,z3,z10,z4,z6]),(0,[z1,z2,z7,z4,z269,z6]),(0,[z1,z2,z954,z4,z5,z6]),(0,[z103,z2,z7,z4,z13,z6]),(1,[z2,z7,z4,z911,z6]),(0,[z1,z2,z7,z4,z5,z955]),(0,[z1,z2,z18,z4,z5,z198]),(0,[z1,z2,z956,z10,z4,z6]),(0,[z1,z2,z32,z7,z10,z37]),(0,[z1,z2,z32,z7,z4,z867])],[(0,[z1,z2,z7,z957,z5,z6])],[(0,[z1,z369,z2,z7,z10,z6]),(0,[z0,z2,z153,z4,z5,z219]),(0,[z1,z2,z7,z4,z5,z958]),(0,[z1,z2,z7,z4,z959,z6]),(0,[z1,z2,z771,z7,z5,z6]),(0,[z1,z2,z113,z7,z10,z6])],[(0,[z1,z2,z960,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z961]),(0,[z1,z2,z7,z4,z962,z6]),(0,[z2,z7,z742,z108,z5,z6]),(0,[z1,z2,z18,z692,z4,z5])],[(0,[z1,z2,z280,z4,z5,z6]),(0,[z1,z2,z963,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z964]),(0,[z1,z2,z7,z4,z5,z965]),(0,[z89,z2,z194,z7,z4,z5]),(0,[z1,z2,z150,z786,z4,z5]),(0,[z1,z2,z7,z10,z317,z6]),(0,[z1,z2,z67,z35,z170,z4])],[(0,[z1,z2,z7,z4,z966,z6]),(0,[z1,z2,z7,z4,z5,z219]),(0,[z1,z2,z7,z4,z5,z967]),(0,[z1,z2,z968,z7,z4,z6]),(0,[z1,z2,z18,z4,z5,z228]),(0,[z1,z2,z51,z7,z712,z176])]],
   [[(0,[z1,z2,z18,z7,z136,z5]),(0,[z1,z2,z32,z7,z4,z137]),(0,[z1,z2,z969,z7,z5,z6]),(0,[z1,z2,z970,z4,z5,z6]),(0,[z496,z1,z43,z4,z5,z6])],[(0,[z1,z2,z971,z7,z4,z6]),(0,[z1,z2,z7,z972,z5,z6]),(0,[z1,z2,z7,z4,z973,z6]),(0,[z1,z825,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z974,z375]),(0,[z1,z2,z33,z777,z5,z6]),(0,[z521,z1,z2,z18,z4,z5])],[(0,[z1,z2,z7,z4,z5,z832]),(0,[z1,z2,z975,z7,z4,z6])],[(0,[z1,z2,z976,z7,z4,z5]),(0,[z140,z2,z7,z60,z5,z6]),(0,[z1,z2,z18,z537,z4,z5]),(0,[z1,z2,z32,z7,z573,z6]),(0,[z1,z2,z977,z7,z4,z5]),(0,[z1,z2,z84,z73,z7,z4]),(0,[z1,z2,z32,z978,z7,z4])],[(0,[z1,z689,z7,z105,z5,z6]),(0,[z1,z2,z33,z4,z5,z20]),(0,[z1,z2,z18,z7,z317,z5]),(0,[z1,z2,z32,z7,z4,z768]),(0,[z1,z2,z357,z68,z7,z6])],[(0,[z1,z2,z7,z979,z4,z5]),(0,[z94,z2,z51,z3,z4,z5]),(0,[z1,z2,z7,z4,z5,z980]),(0,[z1,z2,z18,z7,z981,z5]),(0,[z1,z2,z68,z725,z7,z6])],[(0,[z1,z2,z982,z4,z5,z6]),(0,[z1,z2,z18,z7,z4,z312]),(0,[z1,z2,z983,z7,z4,z6]),(0,[z1,z327,z2,z7,z10,z6]),(0,[z1,z2,z7,z4,z300,z6]),(0,[z1,z984,z7,z4,z5,z6]),(0,[z1,z2,z18,z7,z376,z4]),(0,[z102,z2,z51,z7,z60,z5]),(0,[z1,z2,z7,z4,z5,z985]),(0,[z1,z2,z73,z18,z7,z4]),(0,[z1,z2,z51,z338,z4,z5]),(0,[z1,z2,z57,z7,z4,z176])],[(0,[z1,z2,z306,z4,z5,z6]),(0,[z1,z2,z986,z7,z4,z5]),(0,[z1,z2,z987,z7,z4,z5])]],
   [[(0,[z256,z2,z3,z4,z5,z6]),(0,[z1,z2,z51,z160,z7,z4]),(0,[z1,z2,z335,z18,z4,z64]),(0,[z1,z2,z18,z7,z10,z283]),(0,[z1,z2,z32,z7,z86,z78]),(0,[z1,z2,z32,z387,z7,z6])],[(0,[z1,z2,z7,z4,z5,z230]),(0,[z1,z2,z7,z4,z988,z6]),(0,[z1,z2,z989,z4,z5,z6]),(0,[z1,z2,z990,z7,z5,z6]),(0,[z1,z2,z991,z4,z5,z6]),(0,[z1,z72,z7,z105,z251,z6]),(0,[z1,z2,z18,z511,z4,z5]),(0,[z1,z2,z110,z12,z4,z6]),(0,[z1,z2,z63,z32,z7,z4]),(0,[z1,z2,z18,z7,z992,z5]),(0,[z1,z2,z32,z7,z4,z899])],[(0,[z94,z2,z865,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z31]),(0,[z1,z2,z7,z993,z4,z6]),(0,[z1,z2,z7,z4,z5,z994])],[(0,[z1,z2,z7,z4,z5,z995]),(0,[z1,z2,z996,z7,z4,z5]),(0,[z1,z2,z4,z777,z5,z6]),(0,[z1,z2,z7,z10,z375,z6]),(0,[z1,z717,z7,z10,z4,z6])],[(0,[z1,z2,z7,z4,z5,z997]),(0,[z0,z2,z865,z4,z5,z6]),(0,[z221,z2,z194,z7,z4,z5]),(0,[z1,z2,z18,z304,z4,z5])],[(0,[z1,z2,z51,z306,z4,z5]),(0,[z1,z2,z998,z7,z4,z5]),(0,[z1,z2,z999,z7,z4,z5]),(0,[z1,z2,z51,z7,z4,z1000])],[(0,[z1,z2,z7,z1001,z4,z6]),(0,[z1,z2,z7,z4,z1002,z6]),(0,[z1,z2,z32,z7,z559,z6]),(0,[z1,z2,z7,z4,z330,z6]),(0,[z1,z2,z7,z4,z5,z1003]),(0,[z1,z2,z18,z4,z5,z272]),(0,[z1,z2,z760,z7,z4,z5])],[(0,[z1,z2,z1004,z4,z5,z6]),(0,[z1,z2,z1005,z7,z4,z6])]],
   [[(0,[z1,z2,z1006,z4,z5,z6]),(1,[z1,z799,z4,z5,z6]),(0,[z1,z2,z7,z1007,z4,z6]),(0,[z1,z2,z18,z217,z4,z5]),(0,[z1,z2,z1008,z7,z4,z5]),(0,[z1,z2,z170,z10,z4,z6])],[(0,[z1,z2,z7,z4,z5,z1009]),(0,[z1,z2,z323,z18,z7,z10])],[(0,[z1,z2,z160,z18,z7,z4]),(0,[z42,z1,z799,z4,z5,z6]),(0,[z1,z2,z51,z7,z4,z241]),(0,[z1,z2,z7,z10,z6,z396]),(0,[z1,z2,z23,z7,z4,z156]),(0,[z1,z2,z51,z7,z10,z78])],[(0,[z1,z7,z4,z5,z6,z1010]),(0,[z1,z2,z7,z4,z793,z6]),(0,[z1,z2,z7,z10,z278,z6]),(0,[z1,z2,z7,z350,z4,z6]),(0,[z1,z2,z18,z4,z5,z47]),(0,[z197,z1,z52,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1011]),(0,[z1,z2,z1012,z4,z5,z6]),(0,[z1,z2,z1013,z7,z4,z5]),(0,[z1,z2,z38,z18,z4,z5]),(0,[z1,z2,z18,z659,z4,z5]),(0,[z1,z2,z51,z771,z7,z176]),(0,[z1,z2,z92,z4,z448,z6])],[(0,[z2,z7,z4,z742,z5,z6]),(0,[z1,z2,z323,z33,z5,z367]),(0,[z1,z2,z357,z7,z317,z6]),(0,[z1,z2,z67,z35,z7,z4])],[(0,[z81,z82,z51,z7,z4,z5]),(0,[z1,z2,z18,z7,z4,z300]),(0,[z1,z2,z1014,z4,z5,z6]),(0,[z1,z2,z183,z7,z10,z4]),(0,[z1,z2,z323,z7,z330,z6]),(0,[z98,z1,z7,z185,z4,z6])],[(0,[z1,z2,z7,z10,z650,z6]),(0,[z1,z2,z18,z33,z4,z5])]],
   [[(0,[z1,z2,z1015,z4,z5,z6]),(0,[z1,z2,z691,z7,z10,z6]),(0,[z42,z1,z183,z43,z4,z5])],[(0,[z1,z2,z51,z7,z136,z5]),(0,[z1,z2,z7,z4,z1016,z6]),(0,[z221,z2,z32,z7,z4,z77]),(0,[z1,z2,z217,z4,z5,z152]),(0,[z1,z2,z74,z7,z5,z363]),(0,[z1,z2,z18,z25,z4,z5]),(0,[z1,z2,z51,z7,z716,z4]),(0,[z1,z2,z51,z7,z712,z4]),(0,[z1,z2,z32,z170,z4,z6]),(0,[z1,z2,z1017,z7,z4,z5])],[(0,[z1,z2,z280,z4,z80,z6]),(0,[z81,z82,z280,z4,z5,z6]),(0,[z1,z2,z7,z1018,z5,z6]),(0,[z1,z2,z7,z10,z620,z6]),(0,[z1,z2,z74,z7,z375,z6]),(0,[z1,z46,z2,z32,z18,z4])],[(0,[z1,z2,z1019,z7,z5,z6]),(0,[z0,z2,z153,z10,z4,z6]),(0,[z1,z2,z7,z4,z1020,z6]),(0,[z1,z2,z457,z18,z4,z5]),(0,[z1,z2,z7,z4,z1021,z6])],[(0,[z1,z2,z1022,z4,z5,z6]),(0,[z1,z2,z248,z7,z4,z5]),(0,[z1,z2,z74,z118,z6,z64]),(0,[z1,z2,z293,z4,z6,z47])],[(0,[z1,z2,z51,z7,z508,z5]),(0,[z1,z2,z7,z376,z4,z6]),(0,[z1,z2,z7,z4,z330,z20]),(0,[z1,z2,z7,z4,z5,z720])],[(0,[z1,z2,z7,z10,z4,z6]),(0,[z1,z2,z280,z4,z312,z6])],[(0,[z1,z2,z51,z7,z4,z312]),(0,[z1,z2,z7,z4,z1023,z6]),(0,[z1,z1024,z7,z4,z5,z6]),(0,[z1,z740,z7,z4,z5,z6]),(0,[z0,z2,z153,z4,z5,z326]),(0,[z1,z2,z51,z7,z376,z4]),(0,[z1,z72,z7,z10,z105,z6]),(0,[z1,z19,z7,z4,z5,z152]),(0,[z1,z2,z308,z18,z4,z5]),(0,[z1,z2,z88,z18,z10,z5]),(0,[z1,z2,z323,z33,z375,z6]),(0,[z1,z2,z18,z79,z4,z5]),(0,[z1,z2,z18,z7,z10,z48]),(0,[z1,z2,z18,z786,z4,z5]),(0,[z1,z2,z32,z7,z4,z938])]],
   [[(0,[z1,z2,z960,z7,z508,z6]),(0,[z1,z2,z7,z4,z974,z5]),(1,[z1,z2,z7,z712,z6])],[(0,[z1,z7,z4,z5,z6,z1025]),(0,[z1,z2,z110,z18,z10,z4]),(0,[z1,z2,z357,z217,z4,z6])],[(0,[z1,z2,z7,z4,z5,z326]),(0,[z1,z2,z7,z4,z5,z391]),(0,[z1,z2,z7,z4,z5,z1026]),(0,[z1,z2,z18,z4,z141,z64]),(0,[z1,z2,z63,z118,z4,z64]),(0,[z1,z2,z63,z150,z4,z5]),(0,[z1,z2,z51,z150,z10,z4]),(1,[z1,z2,z217,z10,z6])],[(0,[z1,z2,z306,z4,z80,z6]),(0,[z81,z82,z306,z4,z5,z6]),(0,[z1,z2,z18,z409,z4,z5]),(0,[z1,z2,z7,z4,z5,z363]),(0,[z1,z2,z335,z7,z368,z4])],[(0,[z1,z2,z18,z7,z4,z5]),(0,[z1,z755,z7,z4,z5,z6]),(0,[z1,z2,z7,z10,z498,z6]),(0,[z1,z2,z7,z4,z1027,z6]),(0,[z1,z2,z18,z624,z4,z5]),(0,[z1,z2,z7,z4,z375,z6])],[(0,[z1,z2,z7,z1028,z4,z6]),(0,[z81,z82,z7,z4,z5,z230]),(0,[z1,z2,z51,z7,z4,z70]),(0,[z1,z2,z1029,z7,z4,z5]),(0,[z1,z2,z7,z10,z6,z436]),(0,[z1,z2,z7,z4,z213,z6]),(0,[z1,z2,z1030,z7,z4,z5]),(0,[z1,z72,z18,z7,z105,z5]),(0,[z1,z2,z7,z12,z279,z6]),(0,[z1,z2,z9,z7,z114,z6])],[(0,[z1,z2,z1031,z306,z4,z5]),(0,[z1,z2,z7,z1032,z5,z6]),(0,[z1,z2,z7,z4,z5,z1033]),(0,[z1,z2,z51,z7,z4,z1034]),(0,[z1,z2,z7,z10,z4,z122]),(0,[z1,z2,z7,z114,z4,z6]),(0,[z1,z2,z7,z4,z37,z426])],[(0,[z1,z2,z306,z4,z312,z6]),(0,[z1,z2,z1035,z7,z4,z5]),(0,[z1,z2,z323,z18,z33,z5]),(0,[z1,z2,z63,z18,z4,z5]),(0,[z1,z2,z51,z18,z10,z4])]],
   [[(0,[z1,z2,z949,z7,z4,z5]),(0,[z1,z2,z280,z4,z5,z137]),(0,[z1,z2,z1036,z7,z5,z6]),(0,[z1,z2,z7,z10,z104,z6]),(0,[z1,z2,z7,z4,z5,z133]),(0,[z1,z2,z88,z10,z6,z21])],[(0,[z1,z2,z7,z4,z1037,z6]),(0,[z1,z2,z1038,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z332]),(0,[z490,z2,z7,z4,z5,z146]),(0,[z1,z2,z253,z7,z10,z4]),(0,[z1,z2,z51,z217,z4,z5])],[(0,[z1,z2,z267,z7,z10,z4]),(0,[z1,z2,z7,z10,z145,z6]),(0,[z1,z2,z32,z7,z438,z6]),(0,[z1,z2,z88,z18,z7,z10]),(0,[z1,z2,z7,z4,z5,z1039]),(0,[z1,z2,z807,z7,z4,z6]),(0,[z1,z2,z813,z7,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1040]),(0,[z351,z2,z7,z4,z13,z6]),(0,[z1,z2,z617,z18,z4,z5])],[(0,[z1,z2,z1041,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z34]),(0,[z237,z2,z324,z7,z4,z5])],[(0,[z888,z82,z7,z4,z5,z6]),(0,[z1,z56,z7,z185,z4,z6]),(0,[z1,z2,z7,z10,z4,z20]),(0,[z1,z2,z195,z12,z4,z6]),(0,[z1,z2,z51,z7,z4,z1042]),(0,[z1,z2,z9,z51,z7,z10])],[(0,[z1,z2,z7,z4,z5,z1043]),(0,[z1,z2,z1044,z7,z4,z6]),(0,[z1,z2,z32,z7,z4,z219]),(0,[z1,z7,z105,z905,z5,z6]),(0,[z1,z2,z406,z7,z5,z283]),(0,[z1,z2,z32,z7,z4,z967]),(0,[z1,z2,z7,z177,z4,z37])],[(0,[z1,z2,z7,z4,z1045,z6]),(0,[z1,z2,z51,z7,z4,z300]),(0,[z94,z2,z18,z3,z4,z5]),(0,[z1,z2,z7,z10,z4,z134]),(0,[z1,z2,z7,z4,z1046,z6]),(0,[z1,z2,z51,z618,z4,z5]),(0,[z1,z2,z88,z7,z330,z6]),(0,[z1,z2,z88,z195,z10,z6]),(0,[z1,z2,z968,z7,z4,z367]),(0,[z1,z2,z18,z4,z39,z64]),(0,[z1,z2,z63,z7,z4,z5]),(0,[z1,z2,z18,z7,z4,z1047]),(0,[z1,z2,z51,z7,z10,z4]),(0,[z1,z2,z18,z7,z4,z426])]],
   [[(0,[z1,z2,z18,z167,z4,z5]),(0,[z1,z2,z7,z4,z5,z1048]),(0,[z1,z2,z7,z10,z152,z78]),(0,[z1,z2,z51,z648,z4,z5]),(0,[z1,z475,z290,z7,z4,z6])],[(0,[z1,z2,z306,z4,z5,z137]),(0,[z1,z2,z7,z258,z199,z6]),(0,[z1,z2,z262,z7,z10,z6]),(0,[z1,z2,z217,z86,z5,z78])],[(0,[z1,z2,z7,z4,z1049,z6]),(0,[z1,z2,z35,z79,z4,z5])],[(0,[z1,z2,z7,z508,z5,z6]),(0,[z1,z2,z18,z4,z5,z176])],[(0,[z1,z515,z7,z4,z141,z6]),(0,[z1,z2,z33,z4,z5,z746]),(0,[z1,z2,z834,z10,z4,z6])],[(0,[z603,z1,z2,z18,z4,z5]),(0,[z1,z2,z1050,z7,z4,z6]),(0,[z44,z1,z7,z4,z5,z852]),(0,[z1,z392,z7,z4,z5,z97]),(1,[z1,z2,z88,z18,z10]),(0,[z1,z2,z323,z33,z350,z6]),(0,[z22,z1,z2,z51,z7,z10]),(0,[z1,z2,z357,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z1051]),(0,[z1,z2,z7,z4,z1052,z6]),(0,[z1,z132,z32,z54,z4,z6]),(1,[z1,z2,z777,z5,z6])],[(0,[z1,z2,z1053,z7,z4,z5]),(0,[z1,z2,z1054,z7,z4,z5]),(0,[z1,z2,z51,z357,z7,z4]),(0,[z1,z2,z7,z10,z6,z477]),(0,[z1,z2,z32,z713,z4,z6]),(0,[z1,z2,z7,z325,z5,z78])]],
   [[(0,[z1,z2,z1055,z7,z4,z5]),(0,[z1,z2,z51,z79,z4,z5]),(0,[z1,z2,z51,z7,z10,z48]),(0,[z1,z2,z195,z294,z4,z6]),(0,[z1,z2,z1056,z4,z5,z6]),(0,[z1,z2,z466,z7,z4,z122])],[(0,[z1,z2,z7,z4,z5,z1057]),(0,[z1,z2,z7,z4,z1058,z6]),(0,[z1,z2,z32,z183,z7,z4]),(0,[z1,z2,z7,z652,z5,z78]),(0,[z1,z2,z88,z5,z6,z283]),(0,[z1,z2,z7,z4,z1059,z6]),(0,[z1,z2,z32,z18,z7,z4]),(0,[z1,z2,z79,z10,z4,z6])],[(0,[z81,z82,z7,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z1060]),(0,[z321,z2,z7,z408,z4,z6]),(0,[z1,z2,z1061,z7,z4,z6]),(0,[z1,z2,z7,z712,z5,z6]),(0,[z847,z2,z7,z10,z4,z6]),(0,[z1,z2,z338,z7,z10,z6])],[(0,[z1,z2,z7,z1062,z5,z6]),(0,[z1,z2,z7,z4,z5,z1063]),(0,[z1,z2,z7,z1064,z5,z6]),(0,[z1,z2,z7,z4,z1065,z6]),(0,[z1,z2,z150,z4,z176,z6]),(0,[z1,z2,z771,z7,z176,z6]),(0,[z1,z2,z67,z7,z4,z176]),(0,[z1,z2,z51,z32,z150,z4])],[(0,[z1,z2,z7,z4,z5,z1066]),(0,[z42,z1,z43,z4,z213,z6]),(0,[z1,z2,z18,z7,z4,z241]),(0,[z1,z2,z118,z7,z258,z6]),(0,[z1,z2,z18,z7,z4,z947]),(0,[z1,z2,z7,z4,z781,z6]),(0,[z1,z2,z9,z7,z10,z470]),(0,[z1,z2,z92,z10,z4,z6])],[(0,[z1,z2,z7,z10,z136,z6]),(0,[z1,z2,z7,z10,z6,z493]),(0,[z1,z2,z113,z4,z6,z64]),(0,[z1,z2,z32,z7,z4,z1003]),(0,[z1,z2,z357,z7,z4,z122])],[(0,[z1,z2,z1067,z7,z4,z5]),(0,[z1,z72,z51,z7,z105,z5]),(1,[z1,z2,z7,z10,z122])],[(0,[z1,z2,z7,z4,z1068,z6]),(0,[z1,z2,z1069,z7,z5,z6]),(0,[z1,z2,z7,z1070,z5,z6]),(0,[z1,z2,z110,z18,z4,z156]),(0,[z1,z2,z288,z18,z4,z5]),(0,[z1,z2,z32,z713,z4,z122])]],
   [[(0,[z81,z82,z18,z7,z4,z5]),(0,[z1,z2,z1071,z4,z5,z6]),(0,[z1,z2,z956,z4,z5,z6]),(0,[z1,z7,z4,z905,z5,z6]),(0,[z1,z2,z88,z18,z33,z5]),(0,[z1,z2,z88,z18,z494,z5]),(0,[z1,z2,z118,z4,z6,z47]),(0,[z1,z2,z110,z177,z4,z6]),(0,[z1,z2,z51,z7,z738,z4]),(0,[z1,z2,z7,z336,z5,z78])],[(0,[z1,z2,z7,z10,z508,z6]),(0,[z1,z2,z7,z4,z1072,z6]),(0,[z1,z2,z7,z4,z1073,z6]),(0,[z103,z2,z18,z7,z4,z13]),(0,[z1,z2,z51,z277,z4,z5]),(0,[z1,z2,z632,z7,z10,z6]),(0,[z1,z2,z7,z10,z4,z864]),(0,[z586,z2,z381,z7,z4,z6])],[(0,[z1,z2,z1074,z7,z4,z6]),(0,[z1,z2,z619,z7,z4,z6]),(0,[z1,z2,z7,z1075,z4,z6])],[(0,[z94,z2,z267,z3,z4,z5]),(0,[z1,z2,z32,z333,z7,z4]),(0,[z102,z2,z7,z60,z31,z6]),(0,[z1,z2,z18,z4,z5,z64]),(0,[z1,z2,z936,z7,z4,z6])],[(0,[z1,z2,z7,z1028,z136,z6]),(0,[z842,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1076]),(0,[z1,z2,z7,z4,z65,z34]),(0,[z1,z2,z18,z7,z4,z878]),(0,[z1,z2,z51,z7,z1077,z4]),(0,[z1,z2,z9,z7,z10,z78]),(0,[z1,z2,z7,z4,z5,z1078]),(0,[z1,z2,z1079,z32,z7,z4])],[(0,[z1,z2,z7,z1080,z5,z6]),(0,[z1,z524,z7,z4,z141,z6]),(0,[z1,z2,z18,z7,z972,z5]),(0,[z1,z2,z1008,z7,z10,z4])],[(0,[z1,z2,z1081,z7,z4,z5]),(0,[z1,z2,z1082,z4,z5,z6]),(0,[z270,z1,z7,z4,z5,z97]),(0,[z1,z2,z1083,z7,z4,z5]),(0,[z22,z1,z2,z7,z4,z65]),(0,[z1,z2,z7,z4,z39,z426])],[(0,[z1,z2,z18,z7,z508,z5]),(0,[z2,z7,z4,z911,z224,z6]),(0,[z1,z2,z1084,z7,z4,z6]),(0,[z521,z1,z2,z79,z4,z5])]],
   [[(0,[z1,z2,z7,z10,z4,z137]),(0,[z41,z2,z160,z7,z108,z6]),(0,[z1,z132,z54,z10,z4,z6]),(0,[z1,z2,z7,z4,z5,z822]),(0,[z378,z1,z2,z18,z4,z5]),(0,[z1,z2,z51,z7,z4,z426]),(0,[z1,z2,z359,z7,z10,z6])],[(0,[z1,z2,z7,z1085,z5,z6]),(0,[z1,z2,z7,z4,z5,z1086]),(0,[z1,z2,z18,z7,z4,z190]),(0,[z1,z2,z7,z4,z1087,z6]),(0,[z1,z2,z32,z7,z4,z367]),(0,[z1,z2,z110,z7,z258,z6]),(0,[z1,z2,z35,z7,z258,z6]),(0,[z1,z2,z51,z7,z4,z816])],[(0,[z1,z2,z1088,z4,z5,z6]),(0,[z1,z2,z7,z4,z1089,z6]),(0,[z1,z2,z1090,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1091]),(0,[z1,z2,z7,z10,z39,z78])],[(0,[z2,z865,z3,z4,z5,z6]),(0,[z1,z2,z1092,z7,z5,z6]),(0,[z1,z7,z799,z4,z5,z6]),(0,[z1,z2,z32,z7,z342,z6]),(0,[z1,z2,z7,z4,z39,z156])],[(0,[z1,z295,z7,z4,z5,z152]),(0,[z1,z2,z88,z5,z20,z21]),(0,[z1,z2,z18,z33,z10,z4]),(0,[z1,z2,z7,z4,z65,z78]),(0,[z891,z2,z7,z10,z4,z6])],[(0,[z2,z7,z4,z13,z911,z6]),(0,[z1,z2,z51,z361,z4,z5]),(0,[z1,z2,z68,z7,z375,z6]),(0,[z155,z2,z434,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1093]),(0,[z1,z2,z7,z10,z107,z6]),(0,[z1,z2,z7,z10,z130,z6]),(0,[z1,z2,z7,z258,z224,z6]),(0,[z284,z2,z7,z4,z5,z77]),(0,[z1,z2,z7,z4,z5,z1094]),(0,[z1,z2,z7,z1095,z4,z6]),(0,[z1,z2,z662,z4,z6,z64]),(0,[z1,z2,z7,z4,z1042,z6]),(0,[z1,z2,z7,z4,z881,z6]),(0,[z1,z2,z7,z749,z4,z6]),(0,[z1,z2,z32,z74,z7,z6]),(0,[z1,z2,z18,z195,z4,z5]),(0,[z1,z2,z142,z18,z4,z5])],[(0,[z81,z82,z7,z508,z5,z6]),(0,[z1,z2,z7,z4,z5,z1096]),(0,[z1,z2,z7,z4,z1097,z6]),(0,[z1,z2,z592,z18,z4,z5]),(0,[z1,z2,z18,z7,z4,z70]),(0,[z1,z2,z1098,z7,z4,z6]),(0,[z1,z2,z7,z4,z440,z65]),(0,[z1,z2,z79,z4,z5,z78])]],
   [[(0,[z1,z2,z7,z136,z5,z6]),(0,[z1,z2,z7,z1099,z5,z6]),(0,[z1,z2,z7,z4,z1100,z6]),(0,[z1,z2,z1101,z7,z4,z6]),(0,[z873,z2,z7,z4,z5,z6]),(0,[z42,z1,z32,z43,z4,z6]),(0,[z1,z2,z88,z5,z6,z47]),(0,[z1,z2,z84,z7,z4,z330]),(0,[z1,z2,z7,z10,z86,z78])],[(0,[z1,z2,z1102,z7,z4,z6]),(0,[z1,z2,z248,z7,z10,z4]),(0,[z1,z2,z32,z7,z4,z391]),(0,[z1,z2,z110,z119,z12,z4])],[(0,[z1,z2,z7,z1103,z5,z6]),(0,[z103,z2,z7,z4,z911,z6]),(0,[z1,z2,z7,z4,z1104,z6]),(0,[z1,z2,z32,z7,z4,z363])],[(0,[z1,z2,z865,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1105]),(0,[z1,z2,z7,z4,z5,z1106]),(0,[z1,z2,z203,z7,z10,z6]),(0,[z1,z2,z217,z4,z5,z6]),(0,[z1,z2,z7,z4,z915,z367]),(0,[z1,z2,z749,z4,z5,z6]),(0,[z1,z2,z32,z7,z106,z6]),(0,[z1,z2,z32,z1107,z7,z4]),(0,[z1,z2,z713,z4,z5,z6])],[(0,[z1,z2,z7,z4,z1108,z6]),(0,[z1,z799,z43,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1109])],[(0,[z1,z2,z7,z4,z5,z1110]),(0,[z1,z2,z1111,z7,z4,z5]),(0,[z1,z2,z217,z4,z5,z97]),(0,[z1,z2,z874,z7,z4,z5]),(0,[z334,z1,z245,z7,z4,z5]),(0,[z1,z2,z7,z1077,z4,z6])],[(0,[z1,z2,z1031,z7,z4,z5]),(0,[z1,z2,z7,z1112,z5,z6]),(0,[z1,z2,z7,z4,z1000,z6]),(0,[z41,z2,z7,z742,z5,z6]),(0,[z1,z2,z32,z7,z488,z6]),(0,[z1,z2,z7,z10,z146,z78]),(0,[z1,z2,z7,z4,z5,z1113]),(0,[z1,z7,z4,z802,z5,z6]),(0,[z1,z2,z217,z86,z4,z5])],[(0,[z1,z1114,z7,z4,z5,z6]),(0,[z1,z2,z32,z7,z4,z133]),(0,[z1,z2,z35,z7,z4,z34]),(0,[z1,z2,z51,z7,z4,z820]),(0,[z1,z2,z7,z10,z4,z913])]],
   [[(0,[z1,z2,z7,z4,z1115,z6]),(0,[z1,z2,z7,z4,z241,z6])],[(0,[z2,z888,z7,z4,z5,z6]),(0,[z1,z2,z328,z18,z4,z5]),(0,[z1,z2,z7,z1116,z4,z6]),(0,[z1,z2,z18,z7,z10,z4])],[(0,[z103,z2,z51,z7,z4,z13]),(0,[z1,z2,z7,z4,z5,z1117]),(0,[z1,z2,z7,z1118,z5,z6]),(0,[z1,z2,z84,z32,z7,z4]),(0,[z1,z2,z713,z7,z4,z5])],[(0,[z1,z2,z18,z7,z4,z269]),(0,[z42,z1,z18,z43,z4,z5]),(0,[z1,z2,z1119,z7,z5,z6]),(0,[z1,z2,z7,z4,z39,z34]),(0,[z1,z2,z7,z24,z10,z78]),(0,[z1,z2,z7,z4,z39,z470]),(0,[z1,z2,z713,z4,z5,z122]),(0,[z1,z2,z9,z217,z4,z5]),(0,[z1,z2,z7,z317,z39,z5])],[(0,[z1,z2,z7,z4,z1120,z6]),(0,[z321,z2,z7,z4,z224,z6]),(0,[z1,z2,z1121,z4,z5,z6]),(0,[z1,z2,z88,z18,z5,z283]),(0,[z1,z2,z18,z4,z176,z6]),(0,[z1,z2,z51,z7,z4,z711])],[(0,[z1,z2,z7,z508,z5,z137]),(0,[z1,z2,z608,z18,z4,z5]),(0,[z1,z2,z7,z1122,z5,z6]),(0,[z1,z2,z7,z4,z5,z1123]),(0,[z1,z2,z67,z760,z7,z4])],[(0,[z1,z2,z7,z1124,z5,z6]),(0,[z1,z2,z75,z79,z4,z5])],[(0,[z1125,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z1126,z6]),(0,[z1,z46,z2,z18,z4,z5]),(0,[z1,z2,z51,z895,z7,z4]),(0,[z1,z2,z32,z68,z7,z37])]],
   [[(0,[z1,z2,z7,z4,z5,z1127]),(0,[z1,z2,z217,z4,z5,z146])],[(0,[z1,z2,z7,z4,z1128,z6]),(0,[z221,z2,z7,z10,z4,z77]),(0,[z1,z2,z1129,z7,z4,z6]),(0,[z1,z2,z1130,z7,z4,z6]),(0,[z1,z2,z18,z258,z4,z5]),(0,[z1,z2,z7,z24,z5,z78])],[(0,[z1,z2,z1131,z4,z5,z6]),(0,[z1,z2,z1132,z7,z4,z5]),(0,[z1,z2,z7,z1133,z5,z6]),(0,[z1,z2,z51,z7,z4,z190]),(0,[z1,z2,z7,z4,z1134,z6]),(1,[z1,z7,z4,z5,z852]),(0,[z1,z2,z51,z88,z5,z21]),(0,[z1,z2,z518,z4,z6,z64])],[(0,[z1,z2,z7,z4,z5,z1135]),(0,[z1,z2,z18,z935,z4,z5]),(0,[z1,z2,z67,z35,z7,z317])],[(0,[z50,z2,z7,z4,z5,z729]),(0,[z1,z54,z799,z4,z5,z6]),(0,[z1,z19,z7,z4,z5,z852]),(0,[z1,z2,z63,z7,z10,z4]),(0,[z1,z2,z900,z4,z5,z6])],[(0,[z1,z2,z1136,z4,z5,z6]),(0,[z1,z2,z1137,z7,z4,z5]),(0,[z1,z2,z18,z4,z5,z504]),(0,[z2,z7,z4,z5,z729,z6]),(0,[z1,z2,z7,z4,z5,z1138]),(0,[z1,z2,z18,z7,z117,z4]),(0,[z1,z2,z88,z68,z18,z5])],[(0,[z1,z2,z1139,z7,z4,z5]),(0,[z1,z2,z7,z786,z4,z5])],[(0,[z1,z2,z1140,z7,z4,z5]),(0,[z1,z2,z18,z170,z4,z5]),(1,[z1,z2,z807,z7,z4]),(0,[z1,z2,z357,z7,z86,z78])]],
   [[(0,[z1,z2,z7,z4,z80,z230]),(0,[z1,z212,z7,z17,z5,z6]),(0,[z1,z2,z1141,z7,z4,z5]),(0,[z1,z2,z51,z88,z7,z10])],[(0,[z1,z2,z306,z4,z5,z230]),(0,[z1,z2,z7,z4,z1142,z6])],[(0,[z1,z2,z7,z1143,z5,z6]),(0,[z1,z2,z7,z4,z5,z1144]),(1,[z1,z7,z905,z5,z6]),(0,[z1,z2,z1079,z7,z4,z5]),(0,[z1,z2,z67,z7,z317,z5])],[(0,[z1,z2,z7,z4,z1145,z6]),(0,[z102,z2,z7,z60,z5,z6]),(0,[z579,z2,z7,z4,z13,z6]),(0,[z1,z19,z245,z7,z4,z5]),(0,[z1,z2,z464,z4,z6,z64]),(0,[z1,z2,z51,z750,z7,z4])],[(0,[z81,z82,z7,z136,z5,z6]),(0,[z1,z2,z7,z4,z312,z230]),(0,[z1,z2,z7,z4,z1146,z6]),(0,[z1,z2,z51,z7,z4,z251]),(0,[z1,z2,z18,z258,z5,z6]),(0,[z1,z2,z51,z7,z4,z1142])],[(0,[z1,z1147,z7,z4,z5,z6]),(0,[z1,z2,z1148,z7,z4,z5]),(0,[z1,z2,z33,z172,z5,z6])],[(0,[z1,z2,z1149,z7,z4,z6]),(0,[z1,z2,z1107,z7,z4,z5]),(0,[z1,z2,z51,z975,z7,z4])],[(0,[z41,z2,z32,z7,z108,z6]),(0,[z44,z1,z7,z4,z5,z97]),(0,[z1,z2,z7,z4,z5,z852]),(0,[z1,z2,z308,z7,z10,z6]),(0,[z1,z2,z150,z4,z5,z367]),(0,[z1,z2,z51,z110,z12,z4])]],
   [[(0,[z41,z2,z7,z108,z5,z332]),(0,[z1,z2,z7,z4,z1150,z6]),(0,[z1,z2,z118,z4,z6,z64])],[(0,[z1,z2,z1151,z4,z5,z6]),(0,[z1,z2,z7,z4,z1152,z5]),(0,[z1,z2,z954,z10,z4,z6]),(1,[z1,z2,z725,z7,z6])],[(0,[z1,z2,z1153,z7,z4,z5]),(0,[z2,z7,z4,z5,z729,z146]),(0,[z1,z2,z88,z18,z4,z5]),(0,[z1,z2,z51,z74,z7,z5]),(0,[z1,z2,z7,z258,z5,z363]),(0,[z1,z2,z63,z170,z4,z5])],[(0,[z1,z2,z7,z4,z5,z1154]),(0,[z1,z2,z1155,z7,z4,z5]),(0,[z1,z2,z7,z992,z5,z6]),(0,[z1,z2,z51,z807,z7,z4]),(0,[z1,z2,z308,z177,z4,z6])],[(0,[z1,z2,z7,z4,z5,z1156]),(0,[z1,z2,z51,z7,z4,z269]),(0,[z1,z2,z7,z1157,z4,z6]),(0,[z42,z1,z51,z43,z4,z5]),(0,[z1,z2,z1158,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1159]),(0,[z1,z159,z7,z4,z5,z152]),(0,[z1,z2,z9,z7,z10,z6]),(0,[z1,z2,z217,z10,z6,z78])],[(0,[z1,z2,z280,z10,z4,z6]),(0,[z311,z2,z7,z4,z13,z6]),(0,[z1,z16,z7,z17,z5,z6]),(0,[z1,z2,z7,z4,z735,z5]),(0,[z1,z2,z7,z10,z4,z965]),(0,[z1,z2,z725,z7,z6,z48])],[(0,[z1,z2,z1160,z4,z5,z6]),(0,[z1,z2,z7,z10,z4,z219]),(0,[z1,z2,z328,z12,z4,z6]),(0,[z1,z2,z1161,z7,z4,z5]),(0,[z1,z56,z7,z4,z141,z6]),(0,[z1,z2,z7,z10,z6,z625]),(0,[z1,z2,z12,z749,z4,z6]),(0,[z1,z2,z18,z10,z4,z228])],[(0,[z1,z2,z7,z905,z5,z6]),(0,[z1,z2,z282,z18,z4,z5]),(0,[z1,z2,z63,z35,z7,z4]),(0,[z1,z392,z240,z7,z4,z5]),(0,[z1,z2,z731,z7,z4,z6]),(0,[z22,z1,z2,z7,z336,z5])]],
   [[(0,[z1,z2,z7,z4,z1162,z6]),(0,[z1,z2,z1163,z7,z4,z6]),(0,[z1,z2,z7,z981,z5,z6]),(0,[z1,z2,z7,z4,z1164,z6]),(0,[z1,z2,z51,z7,z4,z959]),(0,[z1,z2,z210,z7,z10,z6])],[(0,[z1,z2,z7,z258,z13,z6]),(0,[z1,z2,z217,z4,z5,z77]),(0,[z1,z2,z206,z7,z10,z6]),(0,[z2,z7,z4,z5,z6,z1165]),(0,[z1,z2,z1166,z7,z4,z5]),(0,[z1,z72,z7,z905,z5,z6]),(0,[z1,z2,z276,z7,z10,z6]),(0,[z1,z2,z7,z712,z176,z6]),(0,[z1,z2,z51,z150,z4,z65])],[(0,[z1,z2,z7,z136,z5,z137]),(0,[z1,z2,z7,z4,z5,z166]),(0,[z1,z2,z51,z531,z4,z5]),(0,[z1,z2,z18,z4,z5,z396])],[(0,[z1,z2,z32,z7,z4,z230]),(0,[z42,z1,z43,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z181]),(0,[z1,z16,z7,z117,z17,z6]),(0,[z1,z2,z7,z4,z5,z1167]),(0,[z1,z2,z7,z10,z6,z629]),(0,[z1,z2,z18,z424,z4,z5]),(0,[z1,z2,z18,z4,z5,z557]),(0,[z1,z2,z32,z7,z279,z6]),(0,[z1,z2,z7,z4,z37,z122]),(0,[z1,z2,z978,z7,z4,z5]),(0,[z1,z2,z32,z725,z7,z6])],[(0,[z1,z2,z261,z4,z6,z64]),(0,[z1,z2,z7,z4,z5,z787]),(0,[z1,z2,z7,z4,z65,z6]),(0,[z1,z2,z308,z7,z258,z6]),(0,[z1,z2,z7,z10,z4,z980])],[(0,[z1,z2,z7,z4,z1168,z6]),(0,[z1,z2,z1169,z7,z4,z5]),(0,[z1170,z2,z7,z4,z5,z6]),(0,[z1,z2,z51,z73,z7,z4]),(0,[z1,z2,z7,z10,z6,z633]),(0,[z1,z2,z110,z18,z368,z4]),(0,[z1,z2,z32,z764,z7,z4]),(0,[z1,z2,z217,z10,z5,z6])],[(0,[z1,z2,z306,z10,z4,z6]),(0,[z1,z2,z7,z4,z1171,z6]),(0,[z41,z2,z7,z108,z5,z166]),(0,[z411,z2,z7,z4,z5,z77]),(0,[z1,z2,z51,z7,z117,z4]),(0,[z1,z2,z18,z4,z199,z64]),(0,[z1,z2,z7,z4,z1172,z6]),(0,[z1,z2,z51,z18,z4,z65])],[(0,[z1,z2,z7,z1173,z4,z6]),(0,[z1,z479,z54,z4,z5,z6]),(0,[z1,z2,z7,z4,z31,z6]),(0,[z1,z2,z489,z18,z4,z5]),(0,[z1,z2,z7,z4,z1174,z6]),(0,[z1,z2,z51,z231,z4,z5]),(0,[z1,z2,z79,z4,z5,z6]),(0,[z1,z2,z935,z4,z5,z64]),(0,[z1,z2,z51,z7,z4,z861])]],
   [[(0,[z1,z2,z7,z4,z1175,z6]),(0,[z1,z2,z18,z4,z5,z570]),(0,[z1,z2,z84,z7,z4,z5]),(0,[z1,z2,z18,z7,z1122,z5]),(0,[z1,z2,z7,z10,z659,z6]),(0,[z1,z2,z35,z7,z4,z65]),(0,[z1,z2,z51,z170,z4,z5]),(0,[z1,z2,z989,z10,z4,z6])],[(0,[z81,z888,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z1034,z6]),(0,[z50,z2,z7,z4,z5,z146]),(0,[z1,z2,z7,z10,z77,z78]),(0,[z1,z2,z7,z1176,z4,z6]),(0,[z1,z16,z7,z905,z5,z6]),(0,[z1,z2,z1177,z7,z4,z5]),(0,[z1,z2,z813,z7,z86,z5])],[(0,[z1,z2,z7,z4,z5,z1178]),(0,[z1,z2,z7,z4,z5,z1179]),(0,[z1,z2,z7,z4,z911,z6]),(0,[z1,z2,z18,z125,z4,z5]),(0,[z1,z2,z953,z4,z5,z6])],[(0,[z1,z2,z7,z1180,z4,z6]),(0,[z1,z2,z1181,z7,z4,z5]),(0,[z94,z2,z3,z4,z5,z6]),(0,[z1,z2,z1182,z7,z4,z6]),(0,[z1,z16,z32,z7,z17,z6]),(0,[z1,z2,z1183,z4,z5,z6]),(0,[z1,z2,z32,z7,z10,z6]),(0,[z1,z2,z7,z279,z5,z6]),(0,[z1,z2,z1184,z4,z5,z6])],[(0,[z1,z2,z7,z1185,z5,z6]),(0,[z1,z2,z7,z1186,z4,z6]),(0,[z1,z2,z1187,z7,z4,z6]),(0,[z1188,z2,z7,z4,z5,z6]),(0,[z1,z132,z18,z54,z4,z5]),(0,[z1,z2,z544,z18,z4,z5]),(0,[z1,z2,z32,z92,z4,z6]),(0,[z1,z2,z35,z760,z7,z4])],[(0,[z1,z2,z7,z742,z5,z6]),(0,[z1,z2,z18,z7,z10,z494]),(0,[z1,z2,z35,z7,z368,z4]),(0,[z1,z2,z7,z10,z6,z78]),(0,[z1,z2,z7,z86,z5,z78])],[(0,[z1,z2,z119,z7,z4,z5]),(0,[z1,z2,z51,z32,z7,z10]),(0,[z1,z2,z32,z7,z4,z1011])],[(0,[z1,z2,z7,z4,z1189,z6]),(0,[z1,z2,z51,z90,z4,z5]),(0,[z1,z2,z7,z712,z4,z6]),(0,[z1,z2,z7,z4,z426,z6])]],
   [[(0,[z1,z2,z18,z635,z4,z5]),(0,[z1,z2,z1190,z7,z4,z5]),(0,[z50,z2,z434,z7,z4,z5]),(0,[z1,z2,z1191,z7,z4,z5]),(0,[z1,z2,z7,z1192,z4,z6])],[(0,[z1,z2,z32,z280,z4,z6]),(0,[z1,z2,z1193,z7,z4,z5]),(0,[z1,z2,z226,z7,z10,z6]),(0,[z1,z2,z7,z4,z5,z1194]),(0,[z1,z2,z1195,z7,z4,z5]),(0,[z1,z2,z1196,z4,z5,z6]),(0,[z1,z2,z32,z18,z33,z4]),(0,[z1,z2,z32,z7,z4,z1117])],[(0,[z1,z2,z280,z508,z5,z6]),(0,[z1,z2,z7,z1197,z5,z6]),(0,[z1,z2,z18,z10,z4,z47])],[(0,[z1,z2,z721,z280,z4,z5]),(0,[z1,z2,z1198,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1199]),(0,[z1,z2,z7,z4,z1200,z6]),(0,[z2,z7,z865,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1201]),(0,[z321,z2,z51,z7,z4,z224]),(0,[z1,z2,z7,z4,z5,z1202]),(0,[z1,z2,z7,z4,z715,z6]),(0,[z1,z2,z23,z4,z6,z64]),(0,[z1,z2,z18,z4,z5,z593]),(0,[z1,z2,z32,z7,z10,z122]),(1,[z1,z2,z32,z713,z4])],[(0,[z1,z2,z7,z4,z5,z1203]),(0,[z1,z2,z7,z4,z5,z1204]),(0,[z1,z2,z7,z1205,z4,z6]),(0,[z1,z2,z1206,z7,z4,z5]),(0,[z1,z7,z4,z5,z852,z152]),(0,[z1,z2,z7,z10,z97,z78]),(0,[z1,z2,z7,z10,z413,z6])],[(0,[z1,z2,z7,z1207,z5,z6]),(0,[z1,z2,z7,z4,z5,z1208]),(0,[z1,z402,z7,z4,z5,z152]),(0,[z1,z2,z18,z208,z4,z5]),(0,[z1,z2,z7,z1209,z5,z6]),(0,[z1,z2,z7,z849,z4,z6]),(0,[z1,z2,z7,z114,z6,z78])],[(0,[z1,z2,z7,z4,z5,z1210]),(0,[z1,z2,z7,z4,z5,z1211]),(0,[z1,z2,z7,z4,z1047,z6]),(0,[z1,z16,z18,z7,z17,z5]),(0,[z1,z2,z150,z258,z5,z6])],[(0,[z1,z2,z7,z4,z1212,z6]),(0,[z1,z2,z7,z4,z5,z1213]),(0,[z1,z2,z1214,z4,z5,z6]),(0,[z237,z2,z7,z4,z5,z146]),(0,[z1,z2,z807,z7,z4,z5])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 505).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1015).take 340) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1355)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [505, 510, 340] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 58).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 58).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 130).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 197).take 59).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [58, 72, 67, 59] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_42868

theorem PEqualNP.Outside.L_meta_42868 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4001949832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4001949832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42868.solve