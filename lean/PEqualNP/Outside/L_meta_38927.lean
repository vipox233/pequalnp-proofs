import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38927

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0021661c6302e316#64 ++ 0x40021661c6302e31#64 ++ 0xb067ee3ce307e73f#64 ++ 0xab067ee3ce307e73#64 : BitVec 256),
   (0x008b06c501696944#64 ++ 0x8008b06c50169694#64 ++ 0xd19b17c703f9f9cf#64 ++ 0x7d19b17c703f9f9c#64 : BitVec 256),
   (0x161418028c1414a9#64 ++ 0x0161418028c1414a#64 ++ 0x7e1c1807fc1e3ffe#64 ++ 0xf7e1c1807fc1e3ff#64 : BitVec 256),
   (0x2b601b6837a03e0e#64 ++ 0x02b601b6837a03e0#64 ++ 0xefe01ff83fe03e0d#64 ++ 0xfefe01ff83fe03e0#64 : BitVec 256),
   (0x4dfea0003adf8000#64 ++ 0x04dfea0003adf800#64 ++ 0x7fffe0003fffc00b#64 ++ 0xe7fffe0003fffc00#64 : BitVec 256),
   (0x8fdfddb7c0000000#64 ++ 0x08fdfddb7c000000#64 ++ 0x8fffffffc0000007#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 4]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb067ee3ce307e73f 0xab067ee3ce307e73

def z1 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19b17c703f9f9cf 0x7d19b17c703f9f9c

def z2 : W := mkw 0x00aa2000224b8000 0x000aa2000224b800 0x71ffe00023ffc00b 0xe71ffe00023ffc00

def z3 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c1807fc1e3ffe 0xf7e1c1807fc1e3ff

def z4 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z5 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z6 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z7 : W := mkw 0x2b6079387682961a 0x42b6079387682961 0x2e64e838fc060630 0x82e64e838fc06063

def z8 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x8fe01ff800000005 0xf8fe01ff80000000

def z9 : W := mkw 0x2b40196014a01c08 0x02b40196014a01c0 0x4f8011c01ce01800 0x54f8011c01ce0180

def z10 : W := mkw 0x12001802840014a9 0x012001802840014a 0x30041807e0063ffe 0xb30041807e0063ff

def z11 : W := mkw 0x000106c501206944 0x8000106c50120694 0x800017c7000039c4 0x1800017c7000039c

def z12 : W := mkw 0x0020601862028212 0x4002060186202821 0x3067e838e307c63b 0xa3067e838e307c63

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x50181007001839ce 0x750181007001839c

def z14 : W := mkw 0x169f1ec78d7d7ded 0x8169f1ec78d7d7de 0xff9f1fc7ffffffff 0xfff9f1fc7fffffff

def z15 : W := mkw 0x008b048500494140 0x8008b04850049414 0x101b00070019c1c2 0x0101b00070019c1c

def z16 : W := mkw 0x2b6019283680160a 0x02b6019283680160 0x2e6008383c000600 0x82e6008383c00060

def z17 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e3e7f800000001 0x081e3e7f80000000

def z18 : W := mkw 0x028b1ec505697d4c 0x8028b1ec505697d4 0xff9b1fc73ff9ffcf 0xfff9b1fc73ff9ffc

def z19 : W := mkw 0x120018000c1414a9 0x0120018000c1414a 0x7e0018003c1e3ffc 0xf7e0018003c1e3ff

def z20 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fe7eff8c0000001 0x88fe7eff8c000000

def z21 : W := mkw 0x008a000000000000 0x0008a00000000000 0x019b000000000003 0x6019b00000000000

def z22 : W := mkw 0x849fc497c0494140 0x8849fc497c049414 0x101fe007c019c1c2 0x0101fe007c019c1c

def z23 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c00003c1e000a 0xe7e1c00003c1e000

def z24 : W := mkw 0x8bcbddb7c0000000 0x08bcbddb7c000000 0x81e3ffffc0000005 0x181e3ffffc000000

def z25 : W := mkw 0x061418000c141408 0x0061418000c14140 0x7e1c18003c1e3e0e 0xf7e1c18003c1e3e0

def z26 : W := mkw 0x002022082302e316 0x4002022082302e31 0x3067e0002307e73b 0xa3067e0002307e73

def z27 : W := mkw 0x008a00c100690840 0x8008a00c10069084 0x419811c300f818c0 0x5419811c300f818c

def z28 : W := mkw 0x00ab66dd636beb56 0xc00ab66dd636beb5 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z29 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z30 : W := mkw 0x2b617f7c77a2ff1e 0x42b617f7c77a2ff1 0xefe3fff83fe1fe0d 0xfefe3fff83fe1fe0

def z31 : W := mkw 0xafffdffff7e97f4e 0x8afffdffff7e97f4 0xfffffffffff9ffcf 0xffffffffffff9ffc

def z32 : W := mkw 0x000164144002c110 0x4000164144002c11 0x1007e004c007c132 0x01007e004c007c13

def z33 : W := mkw 0x2b617f7c77a2ff1e 0x42b617f7c77a2ff1 0xffe7fffcffe7ff3f 0xfffe7fffcffe7ff3

def z34 : W := mkw 0x4dffe61c7bdfe316 0x44dffe61c7bdfe31 0xffffee3cffffe73f 0xeffffee3cffffe73

def z35 : W := mkw 0x0000024001696944 0x8000002400169694 0x0000000003e1c000 0x00000000003e1c00

def z36 : W := mkw 0x0000024001696944 0x8000002400169694 0x5000000003f9f9c8 0x05000000003f9f9c

def z37 : W := mkw 0x008b048500000000 0x0008b04850000000 0x819b17c700000007 0x7819b17c70000000

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x30040804e006273e 0xa30040804e006273

def z39 : W := mkw 0x16357e1eef16f7bf 0x416357e1eef16f7b 0xfe7ffe3fff1fffff 0xffe7ffe3fff1ffff

def z40 : W := mkw 0xcfffffbffbdfe316 0x4cfffffbffbdfe31 0xffffffffffffe73f 0xfffffffffffffe73

def z41 : W := mkw 0x0001461c41006316 0x40001461c4100631 0x80000e3cc0002734 0x080000e3cc000273

def z42 : W := mkw 0x008a00c100690840 0x8008a00c10069084 0x519b11c303f9d8cb 0x7519b11c303f9d8c

def z43 : W := mkw 0x6ffe9b683ffd3e0e 0x06ffe9b683ffd3e0 0xeff81ff83ff83e0d 0xfeff81ff83ff83e0

def z44 : W := mkw 0x8f54d932c0000000 0x08f54d932c000000 0x0e64e838c0000000 0x80e64e838c000000

def z45 : W := mkw 0xcffffdb7fadf8000 0x0cffffdb7fadf800 0xffffffffffffc00f 0xfffffffffffffc00

def z46 : W := mkw 0x0200180004001408 0x0020018000400140 0x6e0018003c003e0c 0xf6e0018003c003e0

def z47 : W := mkw 0x14140002881400a1 0x014140002881400a 0x101c0007c01e01f2 0x0101c0007c01e01f

def z48 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x0fffe00000000003 0xe0fffe0000000000

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0x10040004c0060132 0x010040004c006013

def z50 : W := mkw 0x449e8000085d0000 0x0449e8000085d000 0x0018000000180000 0x0001800000018000

def z51 : W := mkw 0x44bea0002a5f8000 0x044bea0002a5f800 0x307fe000231fc00b 0xa307fe000231fc00

def z52 : W := mkw 0x8fffffffe36beb56 0xc8fffffffe36beb5 0xffffffffe3ffffff 0xfffffffffe3fffff

def z53 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x0f98000000000000 0x40f9800000000000

def z54 : W := mkw 0x16151ec78d347ded 0x816151ec78d347de 0xfe1c1fc7fc1e3ffe 0xffe1c1fc7fc1e3ff

def z55 : W := mkw 0x4d74a0003a968000 0x04d74a0003a96800 0x2e64e0003c060000 0x82e64e0003c06000

def z56 : W := mkw 0x0d7400003a940000 0x00d7400003a94000 0x7ffc00003ffe000b 0xe7ffc00003ffe000

def z57 : W := mkw 0x9f54d932cc1414a9 0x09f54d932cc1414a 0x2e64e838fc060630 0x82e64e838fc06063

def z58 : W := mkw 0xabebdffd77a03e0e 0x0abebdffd77a03e0 0xefe3fff83fe03e0d 0xfefe3fff83fe03e0

def z59 : W := mkw 0xafffdffff7a03e0e 0x0afffdffff7a03e0 0xefffffffffe03e0f 0xfefffffffffe03e0

def z60 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x101fe000001fc002 0x0101fe000001fc00

def z61 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81fbf7ff00000007 0x781fbf7ff0000000

def z62 : W := mkw 0x0bcb1da500000000 0x00bcb1da50000000 0x8ffb1fff00000007 0xf8ffb1fff0000000

def z63 : W := mkw 0x2beb7ffd77ebff5e 0xc2beb7ffd77ebff5 0xffffffffffffffff 0xffffffffffffffff

def z64 : W := mkw 0x000146dd41206b56 0xc000146dd41206b5 0x80001fffc0003ff4 0x180001fffc0003ff

def z65 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x8063e6380301c001 0x08063e6380301c00

def z66 : W := mkw 0x002022082302e316 0x4002022082302e31 0x300000002307e738 0x0300000002307e73

def z67 : W := mkw 0x2020024837a03e0e 0x02020024837a03e0 0x600000003fe03e08 0x0600000003fe03e0

def z68 : W := mkw 0x5ffeb802bedf94a9 0x05ffeb802bedf94a 0x7ffff807ffffffff 0xf7ffff807fffffff

def z69 : W := mkw 0x0001060401006104 0x0000106040100610 0x900306040301e10f 0x2900306040301e10

def z70 : W := mkw 0x8fde99a380000000 0x08fde99a38000000 0x0f9811c300000000 0x50f9811c30000000

def z71 : W := mkw 0x10000000081400a1 0x010000000081400a 0x10000000001e01f0 0x010000000001e01f

def z72 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe41ffcffe63f3f 0xfffe41ffcffe63f3

def z73 : W := mkw 0x0001441440000000 0x0000144144000000 0x8067ee3cc0000007 0xa8067ee3cc000000

def z74 : W := mkw 0x8fdfddb7c8140000 0x08fdfddb7c814000 0xfffffffffc1e000f 0xffffffffffc1e000

def z75 : W := mkw 0x0020200022028000 0x0002020002202800 0x3067e0002307c00b 0xa3067e0002307c00

def z76 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x101c1807c01e3ff6 0x1101c1807c01e3ff

def z77 : W := mkw 0x000164144002c110 0x4000164144002c11 0x0003e0000001c000 0x00003e0000001c00

def z78 : W := mkw 0x5f74b802be9694a9 0x05f74b802be9694a 0x7e7cf807fc1e3ffe 0xf7e7cf807fc1e3ff

def z79 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x6fe3e0003fe1c009 0xe6fe3e0003fe1c00

def z80 : W := mkw 0x000106c501206944 0x8000106c50120694 0xd01817c7001839ce 0x7d01817c7001839c

def z81 : W := mkw 0x89ebe7bd6302e316 0x489ebe7bd6302e31 0xb1e7effce307e73f 0xab1e7effce307e73

def z82 : W := mkw 0x4ddea000085f8000 0x04ddea000085f800 0x1fffe000001fc003 0xe1fffe000001fc00

def z83 : W := mkw 0x0000024001202804 0x0000002400120280 0xc18017c003e0380d 0x7c18017c003e0380

def z84 : W := mkw 0x0021641c6202c312 0x40021641c6202c31 0x3067e83ce007c732 0x83067e83ce007c73

def z85 : W := mkw 0x0dffe61c6302e316 0x40dffe61c6302e31 0xbfffee3ce307e73f 0xebfffee3ce307e73

def z86 : W := mkw 0x82015db7c0000000 0x082015db7c000000 0x80001fffc0000004 0x180001fffc000000

def z87 : W := mkw 0x49ebe61c73cbe316 0x449ebe61c73cbe31 0x81e3e63803e1c001 0x081e3e63803e1c00

def z88 : W := mkw 0x0b617f3c6302e316 0x40b617f3c6302e31 0xbfe7fffce307e73f 0xfbfe7fffce307e73

def z89 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x818307c003e1c001 0x0818307c003e1c00

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x300400002006000a 0xa300400002006000

def z91 : W := mkw 0x6fffff7c7fffff1e 0x46fffff7c7fffff1 0xfffffffcffffff3f 0xffffffffcffffff3

def z92 : W := mkw 0x0020601862028212 0x4002060186202821 0x3064e83ce006273e 0xa3064e83ce006273

def z93 : W := mkw 0x1f741802be9414a9 0x01f741802be9414a 0x7ffc1807fffe3fff 0xf7ffc1807fffe3ff

def z94 : W := mkw 0x0021641462028000 0x0002164146202800 0xb067ee3ce307c00f 0xab067ee3ce307c00

def z95 : W := mkw 0x4021661c7bdfe316 0x44021661c7bdfe31 0xf067ee3cffffe73f 0xaf067ee3cffffe73

def z96 : W := mkw 0x002166dd6322eb56 0xc002166dd6322eb5 0xb067ffffe307ffff 0xbb067ffffe307fff

def z97 : W := mkw 0x4dffa4853adf8000 0x04dffa4853adf800 0xfffff7c73fffc00f 0xffffff7c73fffc00

def z98 : W := mkw 0x0001461c41006316 0x40001461c4100631 0x8000063800000000 0x0800006380000000

def z99 : W := mkw 0x008b46dd41696b56 0xc008b46dd41696b5 0xd19b1fffc3f9ffff 0x7d19b1fffc3f9fff

def z100 : W := mkw 0x008b46d541696944 0x8008b46d54169694 0xd1ffffffc3f9f9cf 0xfd1ffffffc3f9f9c

def z101 : W := mkw 0x8fdfdff7c1696944 0x88fdfdff7c169694 0xdfffffffc3f9f9cf 0xfdfffffffc3f9f9c

def z102 : W := mkw 0x9fdfddb7c81400a1 0x09fdfddb7c81400a 0x9fffffffc01e01f7 0xf9fffffffc01e01f

def z103 : W := mkw 0x14140002881400a1 0x014140002881400a 0x7e1c0007fc1e01fa 0xe7e1c0007fc1e01f

def z104 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xf19f1fc7e3ffffff 0xff19f1fc7e3fffff

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x400010000000380c 0x7400010000000380

def z106 : W := mkw 0x0001461c41006316 0x40001461c4100631 0x90030e3cc301e73f 0x290030e3cc301e73

def z107 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x01e3e00003e1c001 0x001e3e00003e1c00

def z108 : W := mkw 0xbfffdfffffb43eaf 0x0bfffdfffffb43ea 0xfffffffffffe3fff 0xffffffffffffe3ff

def z109 : W := mkw 0x800145b540000000 0x0800145b54000000 0x800007f800000000 0x0800007f80000000

def z110 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xcfffffffdc1818c7 0xfcfffffffdc1818c

def z111 : W := mkw 0x00ab06cd23696b46 0x800ab06cd23696b4 0xf1fb1fff23f9ffcf 0xff1fb1fff23f9ffc

def z112 : W := mkw 0x008b048500000000 0x0008b04850000000 0x818307c000000001 0x0818307c00000000

def z113 : W := mkw 0x2bea1be937e93e4e 0x82bea1be937e93e4 0xeff81ffb3ff83ecd 0xfeff81ffb3ff83ec

def z114 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x4ffbe0001ff9c001 0x44ffbe0001ff9c00

def z115 : W := mkw 0x4dde800018dd0000 0x04dde800018dd000 0x4f9800001cf80000 0x44f9800001cf8000

def z116 : W := mkw 0x0b601b2823002206 0x00b601b282300220 0xafe01ff82300260d 0xfafe01ff82300260

def z117 : W := mkw 0x0001441440000000 0x0000144144000000 0xb067ee3ce006273f 0xab067ee3ce006273

def z118 : W := mkw 0x0ddf848500000000 0x00ddf84850000000 0x8ffff7c700000007 0xf8ffff7c70000000

def z119 : W := mkw 0x12217e1ee702f7bf 0x412217e1ee702f7b 0xb067fe3fe307ffff 0xbb067fe3fe307fff

def z120 : W := mkw 0x22001b6805203e0e 0x022001b6805203e0 0x80001ff800003e04 0x180001ff800003e0

def z121 : W := mkw 0x0614180280000000 0x0061418028000000 0x0e18100300000000 0x50e1810030000000

def z122 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0073ffff9cf 0xf7ffff0073ffff9c

def z123 : W := mkw 0xaf74db7af7a03e0e 0x0af74db7af7a03e0 0xefe4fff8ffe03e0d 0xfefe4fff8ffe03e0

def z124 : W := mkw 0x0000401840000212 0x4000040184000021 0x00000838c0000630 0x000000838c000063

def z125 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe017f81fe01801 0x5cfe017f81fe0180

def z126 : W := mkw 0x3f741b6abfb43eaf 0x03f741b6abfb43ea 0xeff81ffb3ff83ecd 0xfeff81ffb3ff83ec

def z127 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xfff81fff3ff83fcf 0xffff81fff3ff83fc

def z128 : W := mkw 0x8fdfddb7c4001408 0x08fdfddb7c400140 0xeffffffffc003e0f 0xfeffffffffc003e0

def z129 : W := mkw 0x008a024001692804 0x0008a02400169280 0xd19b17c003f9f80f 0x7d19b17c003f9f80

def z130 : W := mkw 0x44bfe61c6b5fe316 0x444bfe61c6b5fe31 0xb07fee3ce31fe73f 0xab07fee3ce31fe73

def z131 : W := mkw 0x6b603b683fffbe0e 0x06b603b683fffbe0 0xffe01ff83ffffe0d 0xfffe01ff83ffffe0

def z132 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x2e040800fc060630 0x82e040800fc06063

def z133 : W := mkw 0x4414a00008168000 0x04414a0000816800 0x0004e00000060000 0x00004e0000006000

def z134 : W := mkw 0x8414c012c0000000 0x08414c012c000000 0x0004e000c0000000 0x00004e000c000000

def z135 : W := mkw 0x8f55ddb7c0000000 0x08f55ddb7c000000 0x8e64ffffc0000004 0x98e64ffffc000000

def z136 : W := mkw 0x0021641c62028212 0x40021641c6202821 0xa067ee3ce0060637 0xaa067ee3ce006063

def z137 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x9067e63cc307c133 0x09067e63cc307c13

def z138 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe007ffffc1fb 0xe7fffe007ffffc1f

def z139 : W := mkw 0x008b048500494140 0x8008b04850049414 0x501b10070019f9ce 0x7501b10070019f9c

def z140 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0x81e007f803e00001 0x081e007f803e0000

def z141 : W := mkw 0x0614180280000000 0x0061418028000000 0x0e1c1807c0000006 0xf0e1c1807c000000

def z142 : W := mkw 0xcdffe5b57adf8000 0x0cdffe5b57adf800 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z143 : W := mkw 0x5ffeb802bedf94a9 0x05ffeb802bedf94a 0x7ffff0033fffd8cb 0xf7ffff0033fffd8c

def z144 : W := mkw 0x0021665c6322eb16 0x40021665c6322eb1 0xf1e7fffce3e7ff3f 0xff1e7fffce3e7ff3

def z145 : W := mkw 0xcffffff7fbffe944 0x8cffffff7fbffe94 0xfffffffffffff9cf 0xffffffffffffff9c

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x501800000018000a 0x6501800000018000

def z147 : W := mkw 0x4dfea0003a968000 0x04dfea0003a96800 0x2fffe0003c060003 0xe2fffe0003c06000

def z148 : W := mkw 0x3f741b6abfb43eaf 0x03f741b6abfb43ea 0xfffc1ffffffe3fff 0xffffc1ffffffe3ff

def z149 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x81e01ff803e03e05 0x181e01ff803e03e0

def z150 : W := mkw 0x8fffddb7f2800000 0x08fffddb7f280000 0xefffffffffe0000f 0xfefffffffffe0000

def z151 : W := mkw 0x008a000000490000 0x0008a00000049000 0x519b000003f9c00b 0x6519b000003f9c00

def z152 : W := mkw 0x120018028c1414a9 0x0120018028c1414a 0x70001807fc1e3ffc 0x170001807fc1e3ff

def z153 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x5e1810071c1839ce 0x75e1810071c1839c

def z154 : W := mkw 0x402020003a968000 0x0402020003a96800 0x200000003c060000 0x0200000003c06000

def z155 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xefe007f83fe00009 0xeefe007f83fe0000

def z156 : W := mkw 0x0614180280000000 0x0061418028000000 0x0e040800c0000000 0x80e040800c000000

def z157 : W := mkw 0x0000024001696944 0x8000002400169694 0x5018100703f9f9ce 0x75018100703f9f9c

def z158 : W := mkw 0x0001661c4102e316 0x40001661c4102e31 0x9007ee3cc007e736 0x09007ee3cc007e73

def z159 : W := mkw 0x2b607b7877a2be1e 0x42b607b7877a2be1 0xefe4fff8ffe63e3d 0xfefe4fff8ffe63e3

def z160 : W := mkw 0x6ffeb9283edf960a 0x06ffeb9283edf960 0x7fffe8383fffc60b 0xe7fffe8383fffc60

def z161 : W := mkw 0x9fdfddb7c40014a9 0x09fdfddb7c40014a 0x8fffffffc0003ff7 0xf8fffffffc0003ff

def z162 : W := mkw 0x402020003adf8000 0x0402020003adf800 0x700000003fffc008 0x0700000003fffc00

def z163 : W := mkw 0x169e18c38c7d1ce9 0x8169e18c38c7d1ce 0x7f9c19c7fcfe3ffe 0xf7f9c19c7fcfe3ff

def z164 : W := mkw 0x0000000000494140 0x8000000000049414 0x100000000019c1c0 0x0100000000019c1c

def z165 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xae601ff83c003e04 0x9ae601ff83c003e0

def z166 : W := mkw 0x5dfea0003edf94a9 0x05dfea0003edf94a 0x7fffe0003ffffffb 0xe7fffe0003ffffff

def z167 : W := mkw 0x449fa6c5097fe944 0x8449fa6c5097fe94 0xd19ff7c703fff9cf 0x7d19ff7c703fff9c

def z168 : W := mkw 0x0000024001696944 0x8000002400169694 0xd18017c003f9f9cd 0x7d18017c003f9f9c

def z169 : W := mkw 0x820019a380000000 0x0820019a38000000 0x000011c300000000 0x1000011c30000000

def z170 : W := mkw 0x2b40196014a01c08 0x02b40196014a01c0 0xcfe01ff81ce01805 0xfcfe01ff81ce0180

def z171 : W := mkw 0x549ea002885f80a1 0x0549ea002885f80a 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z172 : W := mkw 0x969fdc97cc1414a9 0x0969fdc97cc1414a 0x7e1ff807fc1e3ffe 0xf7e1ff807fc1e3ff

def z173 : W := mkw 0x5fffbec7bffffded 0x85fffbec7bffffde 0xffffffc7ffffffff 0xfffffffc7fffffff

def z174 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb067e6382307c00b 0xab067e6382307c00

def z175 : W := mkw 0x008b048500494140 0x8008b04850049414 0x919b17c70019c1c7 0x7919b17c70019c1c

def z176 : W := mkw 0x00202248236beb56 0xc00202248236beb5 0x7000000023fffff8 0x07000000023fffff

def z177 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x5e1c1007dc1e19f2 0x55e1c1007dc1e19f

def z178 : W := mkw 0x0960200032828000 0x0096020003282800 0x7fe7e0003fe7c00b 0xe7fe7e0003fe7c00

def z179 : W := mkw 0x2020024833a02a06 0x02020024833a02a0 0x0000000003e00000 0x00000000003e0000

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067e00000000003 0xa0067e0000000000

def z181 : W := mkw 0x2beb1fed37e97f4e 0x82beb1fed37e97f4 0xfffb1fff3ff9ffcf 0xffffb1fff3ff9ffc

def z182 : W := mkw 0x40ab26c53bffe944 0x840ab26c53bffe94 0xf19b17c73ffff9cf 0x7f19b17c73ffff9c

def z183 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xc19b17c303f9d8c1 0x5c19b17c303f9d8c

def z184 : W := mkw 0x00ab26cd236beb56 0xc00ab26cd236beb5 0xf19b17c723ffffff 0x7f19b17c723fffff

def z185 : W := mkw 0x000164144002c110 0x4000164144002c11 0x9067ee3cc007c137 0xa9067ee3cc007c13

def z186 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x4e1810031c1818c0 0x54e1810031c1818c

def z187 : W := mkw 0x9fffffbfef16f7bf 0x49fffffbfef16f7b 0xffffffffff1fffff 0xfffffffffff1ffff

def z188 : W := mkw 0x4dfea2083bdfe316 0x44dfea2083bdfe31 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z189 : W := mkw 0x049e0000085d0000 0x0049e0000085d000 0x7f9f00003fffc00b 0xe7f9f00003fffc00

def z190 : W := mkw 0x0200180004001408 0x0020018000400140 0x2e0008003c000600 0x82e0008003c00060

def z191 : W := mkw 0x002126042302e104 0x0002126042302e10 0xb067e6042307e10f 0xab067e6042307e10

def z192 : W := mkw 0x008b06c501206944 0x8008b06c50120694 0x819b17c7000039c7 0x7819b17c7000039c

def z193 : W := mkw 0x8f54992280000000 0x08f5499228000000 0x0e00000000000000 0x00e0000000000000

def z194 : W := mkw 0x86155db7c0000000 0x086155db7c000000 0x8e1c1fffc0000006 0xf8e1c1fffc000000

def z195 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e7effcc0000007 0xa81e7effcc000000

def z196 : W := mkw 0x0dde800000490000 0x00dde80000049000 0x5fffe00003f9c00b 0xe5fffe00003f9c00

def z197 : W := mkw 0x002022082302e316 0x4002022082302e31 0x000000000301c000 0x0000000000301c00

def z198 : W := mkw 0x408aa000004b8000 0x0408aa000004b800 0x0003e0000001c000 0x00003e0000001c00

def z199 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x2fe7e0003fe7c001 0x82fe7e0003fe7c00

def z200 : W := mkw 0x0960000032800000 0x0096000003280000 0x6fe000003fe00009 0xe6fe000003fe0000

def z201 : W := mkw 0x0020200022028000 0x0002020002202800 0x2064e00020060000 0x82064e0002006000

def z202 : W := mkw 0x0b401b6001202804 0x00b401b600120280 0xcfe01ff803e0380d 0xfcfe01ff803e0380

def z203 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000001 0xe0fe000000000000

def z204 : W := mkw 0x169f1ec78d7d7ded 0x8169f1ec78d7d7de 0xdf9b17c71ff9f9cf 0x7df9b17c71ff9f9c

def z205 : W := mkw 0x8fdfdfbfc1006316 0x48fdfdfbfc100631 0x8fffffffc0002737 0xf8fffffffc000273

def z206 : W := mkw 0x8fdfddb7c0490000 0x08fdfddb7c049000 0xdfffffffc3f9c00f 0xfdfffffffc3f9c00

def z207 : W := mkw 0x4dffa6c53bffe944 0x84dffa6c53bffe94 0xfffff7c73ffff9cf 0xffffff7c73ffff9c

def z208 : W := mkw 0x2b615f7c77a07f1e 0x42b615f7c77a07f1 0xefe01ffcffe03f3d 0xfefe01ffcffe03f3

def z209 : W := mkw 0xcfdfddb7d8dd0000 0x0cfdfddb7d8dd000 0xcfffffffdcf80007 0xfcfffffffdcf8000

def z210 : W := mkw 0x2020024837a03e0e 0x02020024837a03e0 0xe18017c03fe03e0d 0x7e18017c03fe03e0

def z211 : W := mkw 0x0001060401006104 0x0000106040100610 0x800306000301c001 0x0800306000301c00

def z212 : W := mkw 0x008a00c100690840 0x8008a00c10069084 0x519811c700f839ce 0x7519811c700f839c

def z213 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xdfffffffc01839cf 0xfdfffffffc01839c

def z214 : W := mkw 0x02001a4005203c0c 0x002001a4005203c0 0xef801fc03fe03e0d 0xfef801fc03fe03e0

def z215 : W := mkw 0x402022403bffe944 0x8402022403bffe94 0x700000003ffff9c8 0x0700000003ffff9c

def z216 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x8063ee3cc301e735 0x08063ee3cc301e73

def z217 : W := mkw 0x602022483fffbe0e 0x0602022483fffbe0 0x700000003ffffe08 0x0700000003ffffe0

def z218 : W := mkw 0x2b601b283780360e 0x02b601b283780360 0xae600e383f00260d 0xaae600e383f00260

def z219 : W := mkw 0x2b40196014a01c08 0x02b40196014a01c0 0x6f8019c03ce03e0c 0xf6f8019c03ce03e0

def z220 : W := mkw 0x22001b6805203e0e 0x022001b6805203e0 0xc1801ff803e03e0d 0x7c1801ff803e03e0

def z221 : W := mkw 0x12001802840014a9 0x012001802840014a 0x00001807c0003ff4 0x100001807c0003ff

def z222 : W := mkw 0x1634781aee1696bb 0x41634781aee1696b 0x2e64e838fc060630 0x82e64e838fc06063

def z223 : W := mkw 0x6ffebb683fffbe0e 0x06ffebb683fffbe0 0xfffffff83ffffe0f 0xffffffff83ffffe0

def z224 : W := mkw 0x2b60196036a01c08 0x02b60196036a01c0 0x6fe011c03fe01809 0xf6fe011c03fe0180

def z225 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x3e7fe0003c1fc002 0x83e7fe0003c1fc00

def z226 : W := mkw 0x22217f7c6722ff1e 0x422217f7c6722ff1 0xb067fffce307ff3f 0xbb067fffce307ff3

def z227 : W := mkw 0x0b60192032800000 0x00b6019203280000 0xefe01ff83fe0000d 0xfefe01ff83fe0000

def z228 : W := mkw 0x141400000c1414a9 0x0141400000c1414a 0x7e1c00003c1e3ffa 0xe7e1c00003c1e3ff

def z229 : W := mkw 0x4dffe61c7bdfe316 0x44dffe61c7bdfe31 0xffffe6383fffc00b 0xeffffe6383fffc00

def z230 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xaffffffffc060637 0xfaffffffffc06063

def z231 : W := mkw 0x2000024805203e0e 0x02000024805203e0 0x0000000000003e00 0x00000000000003e0

def z232 : W := mkw 0x0020601862028212 0x4002060186202821 0x2064e838e0060630 0x82064e838e006063

def z233 : W := mkw 0x89cbc7f541696944 0x889cbc7f54169694 0xd1fbf7ff03f9f9cf 0x7d1fbf7ff03f9f9c

def z234 : W := mkw 0x82015db7c0000000 0x082015db7c000000 0x8067ffffc0000007 0xb8067ffffc000000

def z235 : W := mkw 0x12001802840014a9 0x012001802840014a 0x00000800c0000630 0x000000800c000063

def z236 : W := mkw 0x202000083680160a 0x0202000083680160 0x200000003c000600 0x0200000003c00060

def z237 : W := mkw 0x22001b6805203e0e 0x022001b6805203e0 0xee001ff83c003e0c 0xfee001ff83c003e0

def z238 : W := mkw 0x14140002881400a1 0x014140002881400a 0x301c0807e01e27fe 0xa301c0807e01e27f

def z239 : W := mkw 0x2b6019283680160a 0x02b6019283680160 0x6e6018383c003e0c 0xf6e6018383c003e0

def z240 : W := mkw 0x2b611fed37a07f4e 0x82b611fed37a07f4 0xefe01fff3fe03fcd 0xfefe01fff3fe03fc

def z241 : W := mkw 0x220019280400160a 0x0220019280400160 0x0000083800000600 0x0000008380000060

def z242 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xa063ee382301e60d 0xaa063ee382301e60

def z243 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x901b17c70019f9c6 0x1901b17c70019f9c

def z244 : W := mkw 0x1634781aee1696bb 0x41634781aee1696b 0x7e7cf83ffc1e3ffe 0xf7e7cf83ffc1e3ff

def z245 : W := mkw 0x0ddfc41440000000 0x00ddfc4144000000 0x8fffee3cc0000007 0xe8fffee3cc000000

def z246 : W := mkw 0x4dde800018dd0000 0x04dde800018dd000 0x4fffe0001cf80003 0xe4fffe0001cf8000

def z247 : W := mkw 0x82015ff7c1206944 0x882015ff7c120694 0x80001fffc00039c4 0x180001fffc00039c

def z248 : W := mkw 0x2b401b6015a03c0c 0x02b401b6015a03c0 0xcf8017c01fe0380d 0x7cf8017c01fe0380

def z249 : W := mkw 0x0b415d3440000000 0x00b415d344000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z250 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e1818033c183ecc 0xf6e1818033c183ec

def z251 : W := mkw 0x2b603b6837a2be0e 0x02b603b6837a2be0 0xffe7fff83fe7fe0f 0xfffe7fff83fe7fe0

def z252 : W := mkw 0x4000000018dd0000 0x04000000018dd000 0x400000001cf80000 0x0400000001cf8000

def z253 : W := mkw 0x402020003adf8000 0x0402020003adf800 0x7067e0003fffc00b 0xa7067e0003fffc00

def z254 : W := mkw 0x0001048500004140 0x8000104850000414 0x00000007000001c0 0x000000007000001c

def z255 : W := mkw 0x7ffebb6abfffbeaf 0x07ffebb6abfffbea 0xffffffffffffffff 0xffffffffffffffff

def z256 : W := mkw 0x000106c501206944 0x8000106c50120694 0xc18017c703e039cd 0x7c18017c703e039c

def z257 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x001fe007c0000002 0x0001fe007c000000

def z258 : W := mkw 0x16343a0aaf16f7bf 0x416343a0aaf16f7b 0x7e1c1807ff1ffffe 0xf7e1c1807ff1ffff

def z259 : W := mkw 0x6f74bb683fb6be0e 0x06f74bb683fb6be0 0xefe4fff83fe63e0d 0xfefe4fff83fe63e0

def z260 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xf07ffe3fe31fffff 0xff07ffe3fe31ffff

def z261 : W := mkw 0x069f1c8780000000 0x0069f1c878000000 0x8f9f1fc7c0000007 0xf8f9f1fc7c000000

def z262 : W := mkw 0x8f54d932c0000000 0x08f54d932c000000 0x8fe4fff8c0000005 0xf8fe4fff8c000000

def z263 : W := mkw 0x14156416c816c1b1 0x414156416c816c1b 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z264 : W := mkw 0x8fdfdfb7c1006104 0x08fdfdfb7c100610 0x9fffffffc301e10f 0xf9fffffffc301e10

def z265 : W := mkw 0x043420002a168000 0x0043420002a16800 0x7e7fe0003f1fc00b 0xe7e7fe0003f1fc00

def z266 : W := mkw 0x0000020001002004 0x0000002000100200 0x800006000300200d 0x2800006000300200

def z267 : W := mkw 0x5fde98029cdd14a9 0x05fde98029cdd14a 0x7f9c1807fcfe3ffe 0xf7f9c1807fcfe3ff

def z268 : W := mkw 0x8fffffbfe302e316 0x48fffffbfe302e31 0xbfffffffe307e73f 0xfbfffffffe307e73

def z269 : W := mkw 0x8fdfdff7c1696944 0x88fdfdff7c169694 0x8fffffffc3e1c007 0xf8fffffffc3e1c00

def z270 : W := mkw 0x0001064401696944 0x8000106440169694 0xd003060403f9f9cf 0x2d003060403f9f9c

def z271 : W := mkw 0x2b40192014801408 0x02b4019201480140 0x0e0000001c000000 0x00e0000001c00000

def z272 : W := mkw 0x8fdfdff7c1206944 0x88fdfdff7c120694 0x8fffffffc00039c7 0xf8fffffffc00039c

def z273 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e1c1803fc1e1ef0 0xd6e1c1803fc1e1ef

def z274 : W := mkw 0x149f0487885d41e1 0x8149f0487885d41e 0x101f0007c01fc1f2 0x0101f0007c01fc1f

def z275 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x700000003c1e3ff8 0x0700000003c1e3ff

def z276 : W := mkw 0x14140002881400a1 0x014140002881400a 0x00180003001800c0 0x000180003001800c

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e0000003c000008 0xe6e0000003c00000

def z278 : W := mkw 0x0dde800008140000 0x00dde80000814000 0x7fffe0003c1e000b 0xe7fffe0003c1e000

def z279 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x0f8011c000000000 0x50f8011c00000000

def z280 : W := mkw 0x0000004000690840 0x8000000400069084 0x4000000000f818c0 0x04000000000f818c

def z281 : W := mkw 0xaffffffff7a2ff1e 0x4affffffff7a2ff1 0xffffffffffe7ff3f 0xfffffffffffe7ff3

def z282 : W := mkw 0x16155c16cc1414a9 0x016155c16cc1414a 0xfe7ffe3ffc1e3fff 0xffe7ffe3ffc1e3ff

def z283 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e00180000000004 0xf0e0018000000000

def z284 : W := mkw 0xefffffffffffbe0e 0x0efffffffffffbe0 0xfffffffffffffe0f 0xffffffffffffffe0

def z285 : W := mkw 0x008a000000490000 0x0008a00000049000 0x4198000000f80000 0x44198000000f8000

def z286 : W := mkw 0x008a02c101696944 0x8008a02c10169694 0x519811c303f9f9c8 0x5519811c303f9f9c

def z287 : W := mkw 0x09ea000032c90000 0x009ea000032c9000 0x7ffb00003ff9c00b 0xe7ffb00003ff9c00

def z288 : W := mkw 0x3f74192abe9416ab 0x03f74192abe9416a 0x2e640838fc060630 0x82e640838fc06063

def z289 : W := mkw 0xc49fe497c85f8000 0x0c49fe497c85f800 0x101fe007c01fc002 0x0101fe007c01fc00

def z290 : W := mkw 0x16151e068d1475ad 0x016151e068d1475a 0xfe1f1e07ff1fffff 0xffe1f1e07ff1ffff

def z291 : W := mkw 0x06155c16c0000000 0x006155c16c000000 0x8e7ffe3fc0000007 0xf8e7ffe3fc000000

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x4180000003e00009 0x64180000003e0000

def z293 : W := mkw 0x149f06c7897d69e5 0x8149f06c7897d69e 0xd19f17c7c3fff9ff 0x7d19f17c7c3fff9f

def z294 : W := mkw 0xdffffdb7fedf94a9 0x0dffffdb7fedf94a 0xffffffffffffffff 0xffffffffffffffff

def z295 : W := mkw 0x2b611f6c37a07f0e 0x02b611f6c37a07f0 0xffe31ffc3fe1ff0f 0xfffe31ffc3fe1ff0

def z296 : W := mkw 0x8fdf9da780000000 0x08fdf9da78000000 0x8f9b17c700000007 0x78f9b17c70000000

def z297 : W := mkw 0x12001802840014a9 0x012001802840014a 0x00001003000018c0 0x100001003000018c

def z298 : W := mkw 0x1435661eeb16e3b7 0x41435661eeb16e3b 0xb07fee3fe31fe7ff 0xab07fee3fe31fe7f

def z299 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x819b17c703e1c007 0x7819b17c703e1c00

def z300 : W := mkw 0x0021461c63006316 0x40021461c6300631 0xa0600e3ce300273d 0xaa0600e3ce300273

def z301 : W := mkw 0x16141a428d343cad 0x016141a428d343ca 0xff9c1fc7fffe3fff 0xfff9c1fc7fffe3ff

def z302 : W := mkw 0x0000024001202804 0x0000002400120280 0x4000000003e03808 0x04000000003e0380

def z303 : W := mkw 0x141400028c1414a9 0x0141400028c1414a 0x701c0007fc1e3ffa 0x0701c0007fc1e3ff

def z304 : W := mkw 0x4ffeb802badf8000 0x04ffeb802badf800 0x7ffff807ffffc00f 0xf7ffff807ffffc00

def z305 : W := mkw 0x496020003adf8000 0x0496020003adf800 0x7fe000003fffc009 0xe7fe000003fffc00

def z306 : W := mkw 0x0200180004001408 0x0020018000400140 0x7e041804fc063f3e 0xf7e041804fc063f3

def z307 : W := mkw 0x2b603b6837a2ff1e 0x42b603b6837a2ff1 0xffe01ff83fe7ff3d 0xfffe01ff83fe7ff3

def z308 : W := mkw 0xcfde99a398dd0000 0x0cfde99a398dd000 0x4f9811c31cf80000 0x54f9811c31cf8000

def z309 : W := mkw 0x9fde99a38c1414a9 0x09fde99a38c1414a 0x4f9811c31c1818c0 0x54f9811c31c1818c

def z310 : W := mkw 0x16bf7edfef7fffff 0xc16bf7edfef7ffff 0xffffffffffffffff 0xffffffffffffffff

def z311 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xbfffffffe006273f 0xfbfffffffe006273

def z312 : W := mkw 0x3fff1fefbffd7fef 0x83fff1fefbffd7fe 0xffff1fffffffffff 0xfffff1ffffffffff

def z313 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x3e040804fc06273e 0xa3e040804fc06273

def z314 : W := mkw 0x16341a0aaf1436af 0x016341a0aaf1436a 0xfe7c1e3fff1e3fff 0xffe7c1e3fff1e3ff

def z315 : W := mkw 0x00ab26c5236be944 0x800ab26c5236be94 0xf1fff7c723fff9cf 0xff1fff7c723fff9c

def z316 : W := mkw 0x002022082302e316 0x4002022082302e31 0x30040804e307e73e 0xa30040804e307e73

def z317 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe804ffffe73f 0xe7fffe804ffffe73

def z318 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe00ff83fe00601 0x8afe00ff83fe0060

def z319 : W := mkw 0x2f741b683fb43e0e 0x02f741b683fb43e0 0xfffc1ff83ffe3e0f 0xffffc1ff83ffe3e0

def z320 : W := mkw 0x4d54800018940000 0x04d5480001894000 0x0e0000001c000000 0x00e0000001c00000

def z321 : W := mkw 0x4d74a0003a968000 0x04d74a0003a96800 0x3e67e0003f07c00b 0xa3e67e0003f07c00

def z322 : W := mkw 0x8f75ff3ee302e316 0x48f75ff3ee302e31 0xbe67ee3ce307e73f 0xabe67ee3ce307e73

def z323 : W := mkw 0x4ffeb8003edf9408 0x04ffeb8003edf940 0x7ffff8003ffffe0f 0xf7ffff8003ffffe0

def z324 : W := mkw 0x20ab06cd37e97f4e 0x820ab06cd37e97f4 0xf19b17c73ff9ffcf 0x7f19b17c73ff9ffc

def z325 : W := mkw 0x4d74a0003a968000 0x04d74a0003a96800 0x6fe4e0003fe60009 0xe6fe4e0003fe6000

def z326 : W := mkw 0x8fdfddb7c0494140 0x88fdfddb7c049414 0x9fffffffc019c1c7 0xf9fffffffc019c1c

def z327 : W := mkw 0x8fde99a380000000 0x08fde99a38000000 0x8ff81ffb00000005 0xf8ff81ffb0000000

def z328 : W := mkw 0x0001060401006104 0x0000106040100610 0xb0070e04e307e73f 0xab0070e04e307e73

def z329 : W := mkw 0x5ffeb802bedf94a9 0x05ffeb802bedf94a 0x7fffe800ffffc63b 0xe7fffe800ffffc63

def z330 : W := mkw 0x0b40192004001408 0x00b4019200400140 0xefe01ff83c003e0d 0xfefe01ff83c003e0

def z331 : W := mkw 0x228b1fed05697f4e 0x8228b1fed05697f4 0xd19b1fff03f9ffcf 0x7d19b1fff03f9ffc

def z332 : W := mkw 0xcf74f932fa968000 0x0cf74f932fa96800 0x2e64e838fc060000 0x82e64e838fc06000

def z333 : W := mkw 0x2b615f7c77a03e0e 0x02b615f7c77a03e0 0xefe7fffcffe03e0f 0xfefe7fffcffe03e0

def z334 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x519fe00003ffc00b 0x6519fe00003ffc00

def z335 : W := mkw 0x5fde98029cdd14a9 0x05fde98029cdd14a 0x4f9810031cf818c0 0x54f9810031cf818c

def z336 : W := mkw 0x8f74f93ae2028212 0x48f74f93ae202821 0x2e64e838e0060630 0x82e64e838e006063

def z337 : W := mkw 0x169f1c878c5d55e9 0x8169f1c878c5d55e 0x7e1f1807fc1ffffe 0xf7e1f1807fc1ffff

def z338 : W := mkw 0x0000000000490000 0x0000000000049000 0x5000000003f9c008 0x05000000003f9c00

def z339 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81ffffffc0000007 0xf81ffffffc000000

def z340 : W := mkw 0x00ab661c634be316 0x400ab661c634be31 0xf1ffee3ce3ffe73f 0xef1ffee3ce3ffe73

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x20040800e0060630 0x820040800e006063

def z342 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffbf7fb00000001 0x58ffbf7fb0000000

def z343 : W := mkw 0x0001441440004110 0x4000144144000411 0x00000004c0000130 0x000000004c000013

def z344 : W := mkw 0x4d74a0003a968000 0x04d74a0003a96800 0x7e7ce0003c1e000a 0xe7e7ce0003c1e000

def z345 : W := mkw 0x0021060c23006306 0x00021060c2300630 0xb0630e3c2301e70f 0xab0630e3c2301e70

def z346 : W := mkw 0x4dfea2083bdfa206 0x04dfea2083bdfa20 0xffffee383fffe60f 0xeffffee383fffe60

def z347 : W := mkw 0x8fdffdb7c002c110 0x48fdffdb7c002c11 0x9fffffffc007c137 0xf9fffffffc007c13

def z348 : W := mkw 0x40aa20003adf8000 0x040aa20003adf800 0x719b00003fffc00b 0x6719b00003fffc00

def z349 : W := mkw 0x4ddf86c519fd6944 0x84ddf86c519fd694 0xdf9b17c71ff9f9cf 0x7df9b17c71ff9f9c

def z350 : W := mkw 0x102022082f16f7bf 0x4102022082f16f7b 0x700000003f1ffff8 0x0700000003f1ffff

def z351 : W := mkw 0x4dffe4147adf8000 0x04dffe4147adf800 0xffffee3cffffc00f 0xeffffee3cffffc00

def z352 : W := mkw 0x008b048500000000 0x0008b04850000000 0x001b000700000002 0x0001b00070000000

def z353 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x0e0000001c000000 0x00e0000001c00000

def z354 : W := mkw 0x0940012000000000 0x0094001200000000 0x81e007f800000001 0x081e007f80000000

def z355 : W := mkw 0x0020024823202a06 0x00020024823202a0 0xe1e01ff823e03e0d 0xfe1e01ff823e03e0

def z356 : W := mkw 0x0020000822000202 0x0002000082200020 0x2060083820000600 0x8206008382000060

def z357 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x918307c403e1e10f 0x2918307c403e1e10

def z358 : W := mkw 0x0000024001202804 0x0000002400120280 0x818007c003e00001 0x0818007c003e0000

def z359 : W := mkw 0x0200180280000000 0x0020018028000000 0x00001807c0000004 0x100001807c000000

def z360 : W := mkw 0xcdffe497fadf8000 0x0cdffe497fadf800 0x7fffe007ffffc00b 0xe7fffe007ffffc00

def z361 : W := mkw 0x169e18028c5d14a9 0x0169e18028c5d14a 0x7f9f1807ffffffff 0xf7f9f1807fffffff

def z362 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c0800fc1e063a 0xe7e1c0800fc1e063

def z363 : W := mkw 0x0021260c2302e316 0x40021260c2302e31 0xb00306042307e73f 0x2b00306042307e73

def z364 : W := mkw 0x9f54d932cc1414a9 0x09f54d932cc1414a 0x7e7cf83ffc1e3ffe 0xf7e7cf83ffc1e3ff

def z365 : W := mkw 0x2960036837a03e0e 0x02960036837a03e0 0xe1e007f83fe03e09 0x0e1e007f83fe03e0

def z366 : W := mkw 0x443420003adf8000 0x0443420003adf800 0x7e1c00003fffc00a 0xe7e1c00003fffc00

def z367 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x3007e004e307e73a 0x03007e004e307e73

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000020062738 0x0300000002006273

def z369 : W := mkw 0x02217e1c6702f71e 0x402217e1c6702f71 0xfe67fe3cff07ff3f 0xffe67fe3cff07ff3

def z370 : W := mkw 0x0f54192280000000 0x00f5419228000000 0x8ffc1fffc0000007 0xf8ffc1fffc000000

def z371 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19b07c003f9c00b 0x6d19b07c003f9c00

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x818017c000000005 0x7818017c00000000

def z373 : W := mkw 0x0dfe800032800000 0x00dfe80003280000 0x6fffe0003fe0000b 0xe6fffe0003fe0000

def z374 : W := mkw 0x2020224837a2ff1e 0x42020224837a2ff1 0x700000003fe7ff38 0x0700000003fe7ff3

def z375 : W := mkw 0x16343802ae1694a9 0x016343802ae1694a 0x7e7ff807ff1fffff 0xf7e7ff807ff1ffff

def z376 : W := mkw 0x2020024837a03e0e 0x02020024837a03e0 0xe0600e383fe03e0d 0xae0600e383fe03e0

def z377 : W := mkw 0x002062186302e316 0x4002062186302e31 0x3064e838e307e738 0x83064e838e307e73

def z378 : W := mkw 0x49eaa0003adf8000 0x049eaa0003adf800 0x71e3e0003fffc009 0x071e3e0003fffc00

def z379 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xa067ee38e307c631 0x8a067ee38e307c63

def z380 : W := mkw 0x3f741b6abfb43eaf 0x03f741b6abfb43ea 0xefe41ff8ffe63e3d 0xfefe41ff8ffe63e3

def z381 : W := mkw 0x0000024001202804 0x0000002400120280 0x800017c000003804 0x1800017c00000380

def z382 : W := mkw 0x2bea1b6837e93e0e 0x02bea1b6837e93e0 0xfffb1ff83ff9fe0f 0xffffb1ff83ff9fe0

def z383 : W := mkw 0x4d75e61c7b96e316 0x44d75e61c7b96e31 0xbe67ee3cff07e73f 0xabe67ee3cff07e73

def z384 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xefe01fffffe03ffd 0xfefe01fffffe03ff

def z385 : W := mkw 0x0020200822028212 0x4002020082202821 0x2000000020060630 0x0200000002006063

def z386 : W := mkw 0x0001060401006104 0x0000106040100610 0xd01b16070319f9cf 0x7d01b16070319f9c

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000001839c8 0x050000000001839c

def z388 : W := mkw 0x8ddfc497c0000000 0x08ddfc497c000000 0x0fffe007c0000003 0xe0fffe007c000000

def z389 : W := mkw 0x049e800000000000 0x0049e80000000000 0x001fe00000000002 0x0001fe0000000000

def z390 : W := mkw 0x02201a082700360e 0x002201a082700360 0xee601e383f003e0d 0xfee601e383f003e0

def z391 : W := mkw 0x22201a4837a03e0e 0x022201a4837a03e0 0x6e0018003fe03e0c 0xf6e0018003fe03e0

def z392 : W := mkw 0x4ffeb9203adf8000 0x04ffeb9203adf800 0xfffffff83fffc00f 0xffffffff83fffc00

def z393 : W := mkw 0x92015db7c40014a9 0x092015db7c40014a 0x80001fffc0003ff4 0x180001fffc0003ff

def z394 : W := mkw 0x14140002881400a1 0x014140002881400a 0x501c1007c01e39fe 0x7501c1007c01e39f

def z395 : W := mkw 0x0001040400004100 0x0000104040000410 0x100300040001c102 0x0100300040001c10

def z396 : W := mkw 0x0001064401206904 0x0000106440120690 0xd18317c403e1f90f 0x7d18317c403e1f90

def z397 : W := mkw 0x4d74a0003adf8000 0x04d74a0003adf800 0x7e64e0003fffc008 0x87e64e0003fffc00

def z398 : W := mkw 0xcffef932fadf8000 0x0cffef932fadf800 0x7fffe838ffffc00b 0xe7fffe838ffffc00

def z399 : W := mkw 0x002164146202c110 0x4002164146202c11 0x3067e004e307c13b 0xa3067e004e307c13

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x40181003001818c0 0x540181003001818c

def z401 : W := mkw 0x008b04c500694940 0x8008b04c50069494 0x519b11c700f9d9c2 0x5519b11c700f9d9c

def z402 : W := mkw 0x008a02c101692844 0x8008a02c10169284 0xc19817c303f838cd 0x7c19817c303f838c

def z403 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6ffce0003cfe0000 0xc6ffce0003cfe000

def z404 : W := mkw 0x849e808380000000 0x0849e80838000000 0x0018000300000000 0x0001800030000000

def z405 : W := mkw 0x82005932c0000000 0x082005932c000000 0x00000838c0000000 0x000000838c000000

def z406 : W := mkw 0x16357e1eef16f7bf 0x416357e1eef16f7b 0xbe67ee3cff07e73f 0xabe67ee3cff07e73

def z407 : W := mkw 0x2ffe9b6837a03e0e 0x02ffe9b6837a03e0 0xeffffff83fe03e0f 0xfeffffff83fe03e0

def z408 : W := mkw 0x0000004000200800 0x0000000400020080 0x418011c000e01800 0x5418011c000e0180

def z409 : W := mkw 0x4dde80c118fd0840 0x84dde80c118fd084 0x4f9811c31cf818c0 0x54f9811c31cf818c

def z410 : W := mkw 0x100002400d7d7ded 0x8100002400d7d7de 0x700000003ffffff8 0x0700000003ffffff

def z411 : W := mkw 0x000164144002c110 0x4000164144002c11 0x3007e804e007e73e 0xa3007e804e007e73

def z412 : W := mkw 0x8fde99a380000000 0x08fde99a38000000 0x0ffff1c300000003 0xf0ffff1c30000000

def z413 : W := mkw 0xaffe9bebb7a03e0e 0x0affe9bebb7a03e0 0xeff81ffb3fe03e0d 0xfeff81ffb3fe03e0

def z414 : W := mkw 0x0000000008140000 0x0000000000814000 0x700000003c1e0008 0x0700000003c1e000

def z415 : W := mkw 0x22201b6837a03e0e 0x022201b6837a03e0 0xe0001ff83fe03e0c 0x1e0001ff83fe03e0

def z416 : W := mkw 0x008a024001696944 0x8008a02400169694 0x519b000003f9f9cb 0x6519b000003f9f9c

def z417 : W := mkw 0x008a008100000000 0x0008a00810000000 0x019811c300000000 0x5019811c30000000

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0x00040804c0000006 0xa00040804c000000

def z419 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x701810073c1e3ffe 0x7701810073c1e3ff

def z420 : W := mkw 0x0021461c63002206 0x00021461c6300220 0xa067ee3ce300260f 0xaa067ee3ce300260

def z421 : W := mkw 0x22015f7c45207f1e 0x422015f7c45207f1 0x80001ffcc0003f34 0x180001ffcc0003f3

def z422 : W := mkw 0x9fdfdff7cd7d7ded 0x89fdfdff7cd7d7de 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb063e6382307e739 0x0b063e6382307e73

def z424 : W := mkw 0x008b048500000000 0x0008b04850000000 0xd19b17c7001839cf 0x7d19b17c7001839c

def z425 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1c000000000002 0xe0e1c00000000000

def z426 : W := mkw 0x0001461c41006316 0x40001461c4100631 0xb0040e3ce006273e 0xab0040e3ce006273

def z427 : W := mkw 0x2000004014a01c08 0x02000004014a01c0 0x400000001ce01800 0x0400000001ce0180

def z428 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x819ff7c7c0000007 0x7819ff7c7c000000

def z429 : W := mkw 0x6f74b9283e96960a 0x06f74b9283e96960 0x2e64e8383c060600 0x82e64e8383c06060

def z430 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c10033c1e18ca 0xf7e1c10033c1e18c

def z431 : W := mkw 0x4d74e0187a968212 0x44d74e0187a96821 0x2e64e838fc060630 0x82e64e838fc06063

def z432 : W := mkw 0x849fe497c002c110 0x4849fe497c002c11 0x101fe007c007c132 0x0101fe007c007c13

def z433 : W := mkw 0x049f06c5097d6944 0x8049f06c5097d694 0xff9f17c73ffff9cf 0xfff9f17c73ffff9c

def z434 : W := mkw 0x0200192000000000 0x0020019200000000 0x80001ff800000004 0x180001ff80000000

def z435 : W := mkw 0x502020003edf94a9 0x0502020003edf94a 0x700000003ffffff8 0x0700000003ffffff

def z436 : W := mkw 0x44bea0003adf8000 0x044bea0003adf800 0x701fe0003fffc00a 0x0701fe0003fffc00

def z437 : W := mkw 0x0ddf86c501696944 0x80ddf86c50169694 0xdffff7c703f9f9cf 0xfdffff7c703f9f9c

def z438 : W := mkw 0x0020020823002206 0x0002002082300220 0xa0600e382300260d 0xaa0600e382300260

def z439 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x70040804fc1e3ffe 0xa70040804fc1e3ff

def z440 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x0e7fe83fc0000002 0x80e7fe83fc000000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000040000210e 0x2100000040000210

def z442 : W := mkw 0x0b60180036801408 0x00b6018003680140 0x6fe018003fe03e0d 0xf6fe018003fe03e0

def z443 : W := mkw 0xaf74d93af680160a 0x0af74d93af680160 0x2e64e838fc000600 0x82e64e838fc00060

def z444 : W := mkw 0x0021665c636beb56 0xc0021665c636beb5 0xf067ee3ce3ffffff 0xaf067ee3ce3fffff

def z445 : W := mkw 0x0961661c7382e316 0x40961661c7382e31 0xffe7ee3cffe7e73f 0xeffe7ee3cffe7e73

def z446 : W := mkw 0x4dfe80003add0000 0x04dfe80003add000 0x6ff800003ff80009 0xe6ff800003ff8000

def z447 : W := mkw 0x4dfea2403bffe944 0x84dfea2403bffe94 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z448 : W := mkw 0x0200180004001408 0x0020018000400140 0x0000180000003e04 0x10000180000003e0

def z449 : W := mkw 0x2b601b6833a02a06 0x02b601b6833a02a0 0x8fe01ff803e00005 0xf8fe01ff803e0000

def z450 : W := mkw 0x89ca81a100000000 0x089ca81a10000000 0x018001c000000000 0x0018001c00000000

def z451 : W := mkw 0x6dfea2483fffbe0e 0x06dfea2483fffbe0 0x7fffe0003ffffe0b 0xe7fffe0003ffffe0

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018100700000006 0x7001810070000000

def z453 : W := mkw 0x4ddea00018df8000 0x04ddea00018df800 0x5f9fe0001cffc002 0x45f9fe0001cffc00

def z454 : W := mkw 0x0960020833802206 0x0096002083380220 0xefe00e383fe0260d 0xeefe00e383fe0260

def z455 : W := mkw 0x0001461441006104 0x0000146144100610 0x9067ee3cc301e10f 0xa9067ee3cc301e10

def z456 : W := mkw 0x008b068501496144 0x8008b06850149614 0x901b06070319e1cf 0x2901b06070319e1c

def z457 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c0804fc1e273e 0xe7e1c0804fc1e273

def z458 : W := mkw 0x8940c13040000000 0x08940c1304000000 0x0060e03800000000 0x00060e0380000000

def z459 : W := mkw 0x008a000000490000 0x0008a00000049000 0x0183000003e1c001 0x00183000003e1c00

def z460 : W := mkw 0x8ddfc5b540000000 0x08ddfc5b54000000 0x8fffe7f800000003 0xe8fffe7f80000000

def z461 : W := mkw 0x2f741b6ab7a03e0e 0x02f741b6ab7a03e0 0xeffc1fffffe03e0f 0xfeffc1fffffe03e0

def z462 : W := mkw 0x0001040400000000 0x0000104040000000 0x8003060400000007 0x2800306040000000

def z463 : W := mkw 0x5ffffe1effdff7bf 0x45ffffe1effdff7b 0xfffffe3fffffffff 0xffffffe3ffffffff

def z464 : W := mkw 0x0001441440000000 0x0000144144000000 0x0007e004c0000002 0x00007e004c000000

def z465 : W := mkw 0x2beb1fed37e97f4e 0x82beb1fed37e97f4 0xefe31ff83fe1fe0d 0xfefe31ff83fe1fe0

def z466 : W := mkw 0x0960000032800000 0x0096000003280000 0x01e0000003e00001 0x001e0000003e0000

def z467 : W := mkw 0x000106c501206944 0x8000106c50120694 0x900317c70301f9cf 0x3900317c70301f9c

def z468 : W := mkw 0x12011ec785207ded 0x812011ec785207de 0x80001fc7c0003ff4 0x180001fc7c0003ff

def z469 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x8067ee3cc301c007 0xa8067ee3cc301c00

def z470 : W := mkw 0x0000401040000000 0x0000040104000000 0x0064e838c0000000 0x80064e838c000000

def z471 : W := mkw 0x8fde99e380690840 0x88fde99e38069084 0x4f9811c300f818c0 0x54f9811c300f818c

def z472 : W := mkw 0x000106c501696944 0x8000106c50169694 0xd00017c703f9f9cc 0x1d00017c703f9f9c

def z473 : W := mkw 0x2b60196836a01e0a 0x02b60196836a01e0 0x6fe019f83ce01e00 0xd6fe019f83ce01e0

def z474 : W := mkw 0x000000c100200840 0x8000000c10020084 0x000011c3000018c0 0x1000011c3000018c

def z475 : W := mkw 0x000166144102e114 0x4000166144102e11 0x9007e604c307e13f 0x29007e604c307e13

def z476 : W := mkw 0x82217fbfe302e316 0x482217fbfe302e31 0xb067ffffe307e73f 0xbb067ffffe307e73

def z477 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xa1e00ff823e0260d 0xaa1e00ff823e0260

def z478 : W := mkw 0x869fddb7c0000000 0x0869fddb7c000000 0x801fffffc0000006 0x1801fffffc000000

def z479 : W := mkw 0x0fde992000000000 0x00fde99200000000 0x8ffffff800000007 0xf8ffffff80000000

def z480 : W := mkw 0x0001461c41006316 0x40001461c4100631 0x8067ee3cc0002737 0xa8067ee3cc000273

def z481 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7f9800003fffc008 0x47f9800003fffc00

def z482 : W := mkw 0x82015fbfc1006316 0x482015fbfc100631 0x80001fffc0002734 0x180001fffc000273

def z483 : W := mkw 0x2020024837e97f4e 0x82020024837e97f4 0x700000003ff9ffc8 0x0700000003ff9ffc

def z484 : W := mkw 0x6ffeb9603eff9c08 0x06ffeb9603eff9c0 0x7ffff1c03fffd80b 0xf7ffff1c03fffd80

def z485 : W := mkw 0x36141b6a8d343eaf 0x036141b6a8d343ea 0xfe1c1ffffc1e3ffe 0xffe1c1ffffc1e3ff

def z486 : W := mkw 0x4dfee0187adf8212 0x44dfee0187adf821 0x7fffe838ffffc63b 0xe7fffe838ffffc63

def z487 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x9063e63c0301e10f 0x29063e63c0301e10

def z488 : W := mkw 0xa9ebc7fd73a02a06 0x0a9ebc7fd73a02a0 0x81e3e7f803e00001 0x081e3e7f803e0000

def z489 : W := mkw 0x169f1c878c1414a9 0x0169f1c878c1414a 0xff9f1fc7fc1e3fff 0xfff9f1fc7fc1e3ff

def z490 : W := mkw 0x10000002800000a1 0x010000002800000a 0x00000007c00001f0 0x000000007c00001f

def z491 : W := mkw 0xafde99e394a01c08 0x0afde99e394a01c0 0x4f9811c31ce01800 0x54f9811c31ce0180

def z492 : W := mkw 0x36341a4abfb43eaf 0x036341a4abfb43ea 0x7e1c1807fffe3ffe 0xf7e1c1807fffe3ff

def z493 : W := mkw 0x828b5db7c0000000 0x0828b5db7c000000 0x819b1fffc0000007 0x7819b1fffc000000

def z494 : W := mkw 0x0414000280000000 0x0041400028000000 0x001c0007c0000002 0x0001c0007c000000

def z495 : W := mkw 0x0fde980280000000 0x00fde98028000000 0x0ffff807c0000007 0xf0ffff807c000000

def z496 : W := mkw 0x1021661c6f16f7bf 0x41021661c6f16f7b 0xf067ee3cff1fffff 0xaf067ee3cff1ffff

def z497 : W := mkw 0x108b06c50d7d7ded 0x8108b06c50d7d7de 0xf19b17c73fffffff 0x7f19b17c73ffffff

def z498 : W := mkw 0x0414000008140000 0x0041400000814000 0x4e1800001c180000 0x44e1800001c18000

def z499 : W := mkw 0x2961677c73a2eb16 0x42961677c73a2eb1 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z500 : W := mkw 0x4dde800018dd0000 0x04dde800018dd000 0x7f9c00003cfe000a 0xe7f9c00003cfe000

def z501 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xa064ee3ce0062734 0x8a064ee3ce006273

def z502 : W := mkw 0x0020601862028212 0x4002060186202821 0x0060e03800000000 0x00060e0380000000

def z503 : W := mkw 0x2b401b6815a03e0e 0x02b401b6815a03e0 0xcf801ff81ce03e04 0x5cf801ff81ce03e0

def z504 : W := mkw 0x22011fed05207f4e 0x822011fed05207f4 0x80001fff00003fc4 0x180001fff00003fc

def z505 : W := mkw 0x0000000000000000 0x0000000000000000 0x100300000301c00b 0x2100300000301c00

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x701c1807e01e3ffe 0xf701c1807e01e3ff

def z507 : W := mkw 0x4dde800018dd0000 0x04dde800018dd000 0x5f9b00001ff9c00b 0x65f9b00001ff9c00

def z508 : W := mkw 0x8bcbddb540000000 0x08bcbddb54000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z509 : W := mkw 0x6dfea3683bffaa06 0x06dfea3683bffaa0 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z510 : W := mkw 0x2960024837a03e0e 0x02960024837a03e0 0x6fe000003fe03e09 0xe6fe000003fe03e0

def z511 : W := mkw 0x4dffe6dd7bffeb56 0xc4dffe6dd7bffeb5 0xffffffffffffffff 0xffffffffffffffff

def z512 : W := mkw 0x8fde99a380000000 0x08fde99a38000000 0x0f9c19c7c0000006 0xf0f9c19c7c000000

def z513 : W := mkw 0x00ab66dd636beb56 0xc00ab66dd636beb5 0xd1fbf7ff03f9f9cf 0x7d1fbf7ff03f9f9c

def z514 : W := mkw 0x49eba6c533ebe944 0x849eba6c533ebe94 0x81e3e7c003e1c001 0x081e3e7c003e1c00

def z515 : W := mkw 0x0001441440000000 0x0000144144000000 0x8063e63800000001 0x08063e6380000000

def z516 : W := mkw 0x3f74192abe9416ab 0x03f74192abe9416a 0x7e7c183ffc1e3ffe 0xf7e7c183ffc1e3ff

def z517 : W := mkw 0x0200180004001408 0x0020018000400140 0x4e0010001c001800 0x54e0010001c00180

def z518 : W := mkw 0x3f5419629cb41ca9 0x03f5419629cb41ca 0x7f9c19c7fcfe3ffe 0xf7f9c19c7fcfe3ff

def z519 : W := mkw 0x2b617f3c7782f71e 0x42b617f3c7782f71 0xbe67ee3cff07e73f 0xabe67ee3cff07e73

def z520 : W := mkw 0x2b6019283680160a 0x02b6019283680160 0x6fe008383fe00609 0xe6fe008383fe0060

def z521 : W := mkw 0x0435661c6b16e316 0x40435661c6b16e31 0xfe7fee3cff1fe73f 0xefe7fee3cff1fe73

def z522 : W := mkw 0x09eb06c533e96944 0x809eb06c533e9694 0xfffb17c73ff9f9cf 0xffffb17c73ff9f9c

def z523 : W := mkw 0xcfdffdb7c85f8000 0x0cfdffdb7c85f800 0x9fffffffc01fc007 0xf9fffffffc01fc00

def z524 : W := mkw 0x008b048500490000 0x0008b04850049000 0xd19b17c703f9c00f 0x7d19b17c703f9c00

def z525 : W := mkw 0x8f55dd36c0000000 0x08f55dd36c000000 0x8e67ee3cc0000007 0xa8e67ee3cc000000

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x10180007001801c2 0x010180007001801c

def z527 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c10073c1e39ce 0xf7e1c10073c1e39c

def z528 : W := mkw 0x89cbc7f541696944 0x889cbc7f54169694 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z529 : W := mkw 0x0000024001202804 0x0000002400120280 0xd19817c703f839cf 0x7d19817c703f839c

def z530 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x3e1c0807fc1e07f2 0x83e1c0807fc1e07f

def z531 : W := mkw 0x84bfe69fe302e316 0x484bfe69fe302e31 0xb07fee3fe307e73f 0xab07fee3fe307e73

def z532 : W := mkw 0x0020200022028000 0x0002020002202800 0x300000002307c008 0x0300000002307c00

def z533 : W := mkw 0x00ab669d634be356 0xc00ab669d634be35 0xb07fee3fe31fe7ff 0xab07fee3fe31fe7f

def z534 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x31e7e00023e7c00b 0xa31e7e00023e7c00

def z535 : W := mkw 0x0dfea00022028000 0x00dfea0002202800 0x3fffe0002307c00b 0xe3fffe0002307c00

def z536 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xc1e017f803e0380d 0x7c1e017f803e0380

def z537 : W := mkw 0x2940016010a00800 0x02940016010a0080 0x018001c000e00000 0x0018001c000e0000

def z538 : W := mkw 0x008b048500494140 0x8008b04850049414 0x000300000001c000 0x0000300000001c00

def z539 : W := mkw 0x6beabb6837ebbe0e 0x06beabb6837ebbe0 0xefe3fff83fe1fe0d 0xfefe3fff83fe1fe0

def z540 : W := mkw 0x008b06c501202804 0x0008b06c50120280 0xc19b17c703e0380f 0x7c19b17c703e0380

def z541 : W := mkw 0x8fdfddf7c0690840 0x88fdfddf7c069084 0xcfffffffc0f818c7 0xfcfffffffc0f818c

def z542 : W := mkw 0x9fde99a38c1414a9 0x09fde99a38c1414a 0x7f9c19c7fc1e3ffe 0xf7f9c19c7fc1e3ff

def z543 : W := mkw 0x2beb1fed37a03e0e 0x02beb1fed37a03e0 0xeffb1fff3fe03e0f 0xfeffb1fff3fe03e0

def z544 : W := mkw 0x4960a00032828000 0x04960a0003282800 0x0060e00000000000 0x00060e0000000000

def z545 : W := mkw 0x002022082302e316 0x4002022082302e31 0xb0600e382307e73d 0xab0600e382307e73

def z546 : W := mkw 0x4dffa6043bdfe104 0x04dffa6043bdfe10 0xffffe6043fffe10f 0xeffffe6043fffe10

def z547 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8f981fffc0000004 0x58f981fffc000000

def z548 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x6f8011c03fe03e08 0x56f8011c03fe03e0

def z549 : W := mkw 0x2000036801202a06 0x02000036801202a0 0x800007f800000000 0x0800007f80000000

def z550 : W := mkw 0x069f1ec781696944 0x8069f1ec78169694 0xdf9f1fc7c3f9f9cf 0xfdf9f1fc7c3f9f9c

def z551 : W := mkw 0x2960012832800202 0x0296001283280020 0x0060003800000000 0x0006000380000000

def z552 : W := mkw 0x12015e1ec50077bf 0x412015e1ec50077b 0x80001e3fc0003ff4 0x180001e3fc0003ff

def z553 : W := mkw 0x22201b6827203e0e 0x022201b6827203e0 0xa0601ff823003e0d 0xba0601ff823003e0

def z554 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e041800fc063e3c 0xf6e041800fc063e3

def z555 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x11ffe00003ffc003 0x011ffe00003ffc00

def z556 : W := mkw 0x302002483fb43eaf 0x0302002483fb43ea 0x700000003ffe3ff8 0x0700000003ffe3ff

def z557 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xc19817c700f839c4 0x5c19817c700f839c

def z558 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x818317c703e1f9c5 0x1818317c703e1f9c

def z559 : W := mkw 0x008a000000490000 0x0008a00000049000 0x519b100703f9f9cf 0x7519b100703f9f9c

def z560 : W := mkw 0xcffffdb7f2cb8000 0x0cffffdb7f2cb800 0x8fffffffc3e1c007 0xf8fffffffc3e1c00

def z561 : W := mkw 0x4020200032cb8000 0x04020200032cb800 0x0000000003e1c000 0x00000000003e1c00

def z562 : W := mkw 0x949fc497c81400a1 0x0949fc497c81400a 0x101fe007c01e01f2 0x0101fe007c01e01f

def z563 : W := mkw 0x09ca800000000000 0x009ca80000000000 0x01e3e00000000001 0x001e3e0000000000

def z564 : W := mkw 0x0020000032800000 0x0002000003280000 0x600000003fe00008 0x0600000003fe0000

def z565 : W := mkw 0x49eba6c533ebe944 0x849eba6c533ebe94 0xd1fbf7c703f9f9cf 0x7d1fbf7c703f9f9c

def z566 : W := mkw 0x0bcb1fe501696944 0x80bcb1fe50169694 0xdffb1fff03f9f9cf 0xfdffb1fff03f9f9c

def z567 : W := mkw 0xafdfdfffc5203e0e 0x0afdfdfffc5203e0 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z568 : W := mkw 0x14140002881400a1 0x014140002881400a 0x00040000c0060030 0x000040000c006003

def z569 : W := mkw 0x56343802bedf94a9 0x056343802bedf94a 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z571 : W := mkw 0x449fa485085fc140 0x8449fa485085fc14 0x101fe007001fc1c2 0x0101fe007001fc1c

def z572 : W := mkw 0x49ebe61c73cbe316 0x449ebe61c73cbe31 0xb1e7ee3ce3e7e73f 0xab1e7ee3ce3e7e73

def z573 : W := mkw 0x8ffffdbfe2028212 0x48ffffdbfe202821 0xafffffffe0060637 0xfafffffffe006063

def z574 : W := mkw 0x4dffa4853adfc140 0x84dffa4853adfc14 0x7fffe0073fffc1cb 0xe7fffe0073fffc1c

def z575 : W := mkw 0x0000000004001408 0x0000000000400140 0x600000003c003e08 0x0600000003c003e0

def z576 : W := mkw 0xafffdffff3a02a06 0x0afffdffff3a02a0 0x8fffffffc3e00007 0xf8fffffffc3e0000

def z577 : W := mkw 0x5f74b802be9694a9 0x05f74b802be9694a 0x2e64e800fc060630 0x82e64e800fc06063

def z578 : W := mkw 0x10000000040014a9 0x010000000040014a 0x0000000000003ff0 0x00000000000003ff

def z579 : W := mkw 0x849fc6d7c1696944 0x8849fc6d7c169694 0xd19ff7c7c3f9f9cf 0x7d19ff7c7c3f9f9c

def z580 : W := mkw 0x0020200022028000 0x0002020002202800 0x0063e0000301c001 0x00063e0000301c00

def z581 : W := mkw 0x1fde98028c1414a9 0x01fde98028c1414a 0x7ffff807fc1e3fff 0xf7ffff807fc1e3ff

def z582 : W := mkw 0x000020000002c110 0x4000020000002c11 0x100000000007c130 0x0100000000007c13

def z583 : W := mkw 0x0940000010800000 0x0094000001080000 0x4f8000001ce00000 0x44f8000001ce0000

def z584 : W := mkw 0x0614180280000000 0x0061418028000000 0x3e1c1807e006273e 0xf3e1c1807e006273

def z585 : W := mkw 0x16141802840014a9 0x016141802840014a 0x0e1c1807c0003ff6 0xf0e1c1807c0003ff

def z586 : W := mkw 0x008a00c100690840 0x8008a00c10069084 0x018001c000e00000 0x0018001c000e0000

def z587 : W := mkw 0x0020020823002206 0x0002002082300220 0x8060063803000001 0x0806006380300000

def z588 : W := mkw 0x0414000008140000 0x0041400000814000 0x101c0000001e0002 0x0101c0000001e000

def z589 : W := mkw 0x3f757f7effb6ffbf 0x43f757f7effb6ffb 0xffffffffffffffff 0xffffffffffffffff

def z590 : W := mkw 0x2200196004201c08 0x02200196004201c0 0x000011c000001800 0x1000011c00000180

def z591 : W := mkw 0x8f54d932c0000000 0x08f54d932c000000 0x0e7cf83fc0000006 0xf0e7cf83fc000000

def z592 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x200000003c060630 0x0200000003c06063

def z593 : W := mkw 0x4dffa6c53bffe944 0x84dffa6c53bffe94 0xffffe7c03fffc00b 0xeffffe7c03fffc00

def z594 : W := mkw 0x008b048500494140 0x8008b04850049414 0x519b000703f9c1cb 0x6519b000703f9c1c

def z595 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1810033c1e3ff8 0x57e1810033c1e3ff

def z596 : W := mkw 0xa2015fffc5203e0e 0x0a2015fffc5203e0 0x80001fffc0003e04 0x180001fffc0003e0

def z597 : W := mkw 0x16141802881400a1 0x016141802881400a 0x1e1c1807c01e01f6 0xf1e1c1807c01e01f

def z598 : W := mkw 0x29eb07ed33e96b46 0x829eb07ed33e96b4 0x81e307f803e1c001 0x081e307f803e1c00

def z599 : W := mkw 0x128b1ec785697ded 0x8128b1ec785697de 0xd19b1fc7c3f9ffff 0x7d19b1fc7c3f9fff

def z600 : W := mkw 0x40002000085f8000 0x040002000085f800 0x10000000001fc000 0x010000000001fc00

def z601 : W := mkw 0x0000020801002206 0x0000002080100220 0x80000e3800002604 0x080000e380000260

def z602 : W := mkw 0x000106c501206944 0x8000106c50120694 0x800007c000000000 0x0800007c00000000

def z603 : W := mkw 0x002062186302a216 0x4002062186302a21 0xa064ee38e306263d 0xaa064ee38e306263

def z604 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x2e1c1807fc060636 0xf2e1c1807fc06063

def z605 : W := mkw 0x0000024001206944 0x8000002400120694 0x00000000000039c0 0x000000000000039c

def z606 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x0f9ff1c7c0000002 0x50f9ff1c7c000000

def z607 : W := mkw 0x008a000000490000 0x0008a00000049000 0x101b00000019c002 0x0101b00000019c00

def z608 : W := mkw 0x0960000032800000 0x0096000003280000 0x2e6000003c000000 0x82e6000003c00000

def z609 : W := mkw 0x8fdf9fe781696944 0x88fdf9fe78169694 0xdf9b17c703f9f9cf 0x7df9b17c703f9f9c

def z610 : W := mkw 0x8fded932c0000000 0x08fded932c000000 0x0fffe838c0000003 0xe0fffe838c000000

def z611 : W := mkw 0x8ffffdb7e2028000 0x08ffffdb7e202800 0xbfffffffe307c00f 0xfbfffffffe307c00

def z612 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e040800fc1e3ff8 0x87e040800fc1e3ff

def z613 : W := mkw 0x16141a428d7d7ded 0x816141a428d7d7de 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z614 : W := mkw 0xcffffdb7fa968000 0x0cffffdb7fa96800 0xaffffffffc060007 0xfaffffffffc06000

def z615 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd18307c003f9f9c9 0x0d18307c003f9f9c

def z616 : W := mkw 0x808bc49540000000 0x0808bc4954000000 0x0003e00000000000 0x00003e0000000000

def z617 : W := mkw 0x80014497c0000000 0x080014497c000000 0x00000007c0000000 0x000000007c000000

def z618 : W := mkw 0x0001060401006104 0x0000106040100610 0x8000060400002104 0x0800006040000210

def z619 : W := mkw 0x402022083bdfe316 0x4402022083bdfe31 0x700000003fffe738 0x0700000003fffe73

def z620 : W := mkw 0x2961677c73a2eb16 0x42961677c73a2eb1 0xb1e7effce3e7e73f 0xab1e7effce3e7e73

def z621 : W := mkw 0x0020020823002206 0x0002002082300220 0x2000000023002608 0x0200000002300260

def z622 : W := mkw 0x0614180280000000 0x0061418028000000 0x5e1c1807c01839ce 0xf5e1c1807c01839c

def z623 : W := mkw 0x29eb07ed33e96b46 0x829eb07ed33e96b4 0xd1fb17ff03f9f9cf 0x7d1fb17ff03f9f9c

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x80600e3800000005 0xa80600e380000000

def z625 : W := mkw 0x12001802840014a9 0x012001802840014a 0x6e001807fc003ffc 0xf6e001807fc003ff

def z626 : W := mkw 0x1f5419228c1414a9 0x01f5419228c1414a 0xfffc1ffffc1e3fff 0xffffc1ffffc1e3ff

def z627 : W := mkw 0x2b401b6805203e0e 0x02b401b6805203e0 0x8fe01ff800003e05 0xf8fe01ff800003e0

def z628 : W := mkw 0x0614180284001408 0x0061418028400140 0x6e1c1807fc003e0e 0xf6e1c1807fc003e0

def z629 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb0000e3ce307e73c 0x0b0000e3ce307e73

def z630 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x400000001c1818c0 0x0400000001c1818c

def z631 : W := mkw 0x8fdfdff7c1202804 0x08fdfdff7c120280 0xcfffffffc3e0380f 0xfcfffffffc3e0380

def z632 : W := mkw 0x0960024033a02804 0x00960024033a0280 0xefe017c03fe0380d 0xfefe017c03fe0380

def z633 : W := mkw 0xc9ebe5b572cb8000 0x0c9ebe5b572cb800 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z634 : W := mkw 0x2b6019283680160a 0x02b6019283680160 0xafe01ff83c000605 0xfafe01ff83c00060

def z635 : W := mkw 0x8ddfc5b7c0000000 0x08ddfc5b7c000000 0x81ffe7ffc0000003 0x081ffe7ffc000000

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000804c0002734 0x000000804c000273

def z637 : W := mkw 0x16155e1ecd1477bf 0x416155e1ecd1477b 0xfe1c1e3ffc1e3ffe 0xffe1c1e3ffc1e3ff

def z638 : W := mkw 0x06357e1ee302e316 0x406357e1ee302e31 0xbe7ffe3fe307e73f 0xfbe7ffe3fe307e73

def z639 : W := mkw 0x828b5ff7c1696944 0x8828b5ff7c169694 0xd19b1fffc3f9f9cf 0x7d19b1fffc3f9f9c

def z640 : W := mkw 0xcffeb9a3badf8000 0x0cffeb9a3badf800 0x7ffff1c33fffc00b 0xf7ffff1c33fffc00

def z641 : W := mkw 0x8fded9b3c0000000 0x08fded9b3c000000 0x0ffcf9fbc0000000 0xd0ffcf9fbc000000

def z642 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x4e1c1807dc1818c6 0xf4e1c1807dc1818c

def z643 : W := mkw 0x4dfea2403bffa804 0x04dfea2403bffa80 0xfffff7c03ffff80f 0xffffff7c03ffff80

def z644 : W := mkw 0x0614180288140000 0x0061418028814000 0x7e1c1807fc1e000e 0xf7e1c1807fc1e000

def z645 : W := mkw 0x008b6495404bc150 0xc008b6495404bc15 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z646 : W := mkw 0x0000601040028010 0x4000060104002801 0x0004e000c0060030 0x00004e000c006003

def z647 : W := mkw 0x008b068501006104 0x0008b06850100610 0x919b17c70301e10f 0x7919b17c70301e10

def z648 : W := mkw 0x00ab66dd636beb56 0xc00ab66dd636beb5 0xb1e7effce3e7e73f 0xab1e7effce3e7e73

def z649 : W := mkw 0x0001048500000000 0x0000104850000000 0x800017c700000004 0x1800017c70000000

def z650 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x7e1fe0003c1fc00a 0xe7e1fe0003c1fc00

def z651 : W := mkw 0x002022082302a206 0x0002022082302a20 0xb067ee382307e60f 0xab067ee382307e60

def z652 : W := mkw 0x6fde99601cfd1c08 0x06fde99601cfd1c0 0x4f9811c01cf81800 0x54f9811c01cf8180

def z653 : W := mkw 0x0020000022000000 0x0002000002200000 0x2060000023000009 0xa206000002300000

def z654 : W := mkw 0x2bcb1fe515e97d4c 0x82bcb1fe515e97d4 0xdf9b17c71ff9f9cf 0x7df9b17c71ff9f9c

def z655 : W := mkw 0x0200180004001408 0x0020018000400140 0x7e1818073c183fce 0xf7e1818073c183fc

def z656 : W := mkw 0x569eb8028c5f94a9 0x0569eb8028c5f94a 0x7e1ff807fc1ffffe 0xf7e1ff807fc1ffff

def z657 : W := mkw 0x8fffdfbfe3002206 0x08fffdfbfe300220 0xafffffffe300260f 0xfafffffffe300260

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001007000039c4 0x100001007000039c

def z659 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x4e181807dc183ff4 0x54e181807dc183ff

def z660 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x501b000703f9f9ca 0x0501b000703f9f9c

def z661 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x0e60083800000000 0x80e6008380000000

def z662 : W := mkw 0x0000020001006104 0x0000002000100610 0x100000000301e108 0x0100000000301e10

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x200008002000260c 0xa200008002000260

def z664 : W := mkw 0x6fffbfed3fffff4e 0x86fffbfed3fffff4 0xffffffff3fffffcf 0xfffffffff3fffffc

def z665 : W := mkw 0xab615ffff7a03e0e 0x0ab615ffff7a03e0 0xefe01fffffe03e0d 0xfefe01fffffe03e0

def z666 : W := mkw 0x008b66d5416be954 0xc008b66d5416be95 0xd19ff7c7c3fff9ff 0x7d19ff7c7c3fff9f

def z667 : W := mkw 0x32001b6a85203eaf 0x032001b6a85203ea 0x80001fffc0003ff4 0x180001fffc0003ff

def z668 : W := mkw 0x4dffe4147adfc110 0x44dffe4147adfc11 0x7fffe004ffffc13b 0xe7fffe004ffffc13

def z669 : W := mkw 0x4dfea0c13aff8840 0x84dfea0c13aff884 0x7ffff1c33fffd8cb 0xf7ffff1c33fffd8c

def z670 : W := mkw 0x169e18c38c7d1ce9 0x8169e18c38c7d1ce 0x4f9811c31cf818c0 0x54f9811c31cf818c

def z671 : W := mkw 0x869fdc97c0000000 0x0869fdc97c000000 0x0e1ff807c0000006 0xf0e1ff807c000000

def z672 : W := mkw 0x96155db7cc1414a9 0x096155db7cc1414a 0xfe1c1ffffc1e3ffe 0xffe1c1ffffc1e3ff

def z673 : W := mkw 0x008a008100490040 0x8008a00810049004 0x00180003001800c0 0x000180003001800c

def z674 : W := mkw 0x0020200022028000 0x0002020002202800 0x3067e804e307e73f 0xa3067e804e307e73

def z675 : W := mkw 0x00ab66dd636beb56 0xc00ab66dd636beb5 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z676 : W := mkw 0x49ca800010c90000 0x049ca800010c9000 0x0180000000e00000 0x00180000000e0000

def z677 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x919b07c703f9c1c3 0x0919b07c703f9c1c

def z678 : W := mkw 0x2021665c77a2ff1e 0x42021665c77a2ff1 0xf067ee3cffe7ff3f 0xaf067ee3cffe7ff3

def z679 : W := mkw 0x8fffffbfe302e316 0x48fffffbfe302e31 0x8fffffffc301c007 0xf8fffffffc301c00

def z680 : W := mkw 0x0000020801006316 0x4000002080100631 0x0000000000002730 0x0000000000000273

def z681 : W := mkw 0x00ab669d6302e316 0x400ab669d6302e31 0xb1ffffffe307e73f 0xfb1ffffffe307e73

def z682 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x6e6008383fe03e08 0x86e6008383fe03e0

def z683 : W := mkw 0x69eaa36833ebaa06 0x069eaa36833ebaa0 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z684 : W := mkw 0x008b060401496104 0x0008b06040149610 0xd19b060403f9e10f 0x6d19b060403f9e10

def z685 : W := mkw 0x12001802840014a9 0x012001802840014a 0x50181807c0183ffe 0x750181807c0183ff

def z686 : W := mkw 0x16157c16cc16d5b9 0x416157c16cc16d5b 0x7e1ff807fc1ffffe 0xf7e1ff807fc1ffff

def z687 : W := mkw 0x0000200000028000 0x0000020000002800 0x1007e0000007c002 0x01007e0000007c00

def z688 : W := mkw 0x0414000008140000 0x0041400000814000 0x2e0400003c060000 0x82e0400003c06000

def z689 : W := mkw 0x008b04c500690840 0x8008b04c50069084 0xc19b17c700f818c7 0x7c19b17c700f818c

def z690 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x2e041807fc063ff4 0x92e041807fc063ff

def z691 : W := mkw 0x0d54800000000000 0x00d5480000000000 0x0e64e00000000000 0x80e64e0000000000

def z692 : W := mkw 0x0020020823002206 0x0002002082300220 0xb0640e3ce306273f 0xab0640e3ce306273

def z693 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xc18317c003e1f80d 0x7c18317c003e1f80

def z694 : W := mkw 0xafdfddf7d4a01c08 0x0afdfddf7d4a01c0 0xcfffffffdce01807 0xfcfffffffdce0180

def z695 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x807fee3fc0000007 0xa807fee3fc000000

def z696 : W := mkw 0x2bca19e114e91c48 0x82bca19e114e91c4 0x4f9811c31cf818c0 0x54f9811c31cf818c

def z697 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x51fbe00003f9c00b 0x651fbe00003f9c00

def z698 : W := mkw 0x3b601b683fb43eaf 0x03b601b683fb43ea 0xffe01ff83ffe3ffd 0xfffe01ff83ffe3ff

def z699 : W := mkw 0x449fe414485fc110 0x4449fe414485fc11 0x101fe004c01fc132 0x0101fe004c01fc13

def z700 : W := mkw 0x3f5419629cb41ca9 0x03f5419629cb41ca 0x4f9811c31cf818c0 0x54f9811c31cf818c

def z701 : W := mkw 0x2b601b6837e97f4e 0x82b601b6837e97f4 0xffe01ff83ff9ffcd 0xfffe01ff83ff9ffc

def z702 : W := mkw 0x4dfea00032cb8000 0x04dfea00032cb800 0x0fffe00003e1c003 0xe0fffe00003e1c00

def z703 : W := mkw 0x89ebe7bd6302e316 0x489ebe7bd6302e31 0x81e3e7f80301c001 0x081e3e7f80301c00

def z704 : W := mkw 0x8b415db7c0000000 0x08b415db7c000000 0x8fe01fffc0000005 0xf8fe01fffc000000

def z705 : W := mkw 0x0001441440000000 0x0000144144000000 0x80000e3cc0000004 0x080000e3cc000000

def z706 : W := mkw 0xafffddbff680160a 0x0afffddbff680160 0xaffffffffc000607 0xfaffffffffc00060

def z707 : W := mkw 0x2b603b6837a2be1e 0x42b603b6837a2be1 0xefe01ff83fe63e3d 0xfefe01ff83fe63e3

def z708 : W := mkw 0x9fdfddb7c40014a9 0x09fdfddb7c40014a 0x8fffffffc00018c7 0xf8fffffffc00018c

def z709 : W := mkw 0xa2015fffc5207f4e 0x8a2015fffc5207f4 0x80001fffc0003fc4 0x180001fffc0003fc

def z710 : W := mkw 0xdf74f932fe9694a9 0x0df74f932fe9694a 0x2e64e838fc060630 0x82e64e838fc06063

def z711 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ffcffe03f3d 0xfefe01ffcffe03f3

def z712 : W := mkw 0x002166dd6322eb56 0xc002166dd6322eb5 0xb067effce307e73f 0xab067effce307e73

def z713 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x9067ee3cc307e737 0x09067ee3cc307e73

def z714 : W := mkw 0x2b603b6837a2be0e 0x02b603b6837a2be0 0xffe7fffcffe7ff3f 0xfffe7fffcffe7ff3

def z715 : W := mkw 0x008a02c101696944 0x8008a02c10169694 0x419811c303f9d8c0 0x5419811c303f9d8c

def z716 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fe7e0003fffc009 0x87fe7e0003fffc00

def z717 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0043fffe10f 0xe7fffe0043fffe10

def z718 : W := mkw 0x2020224833a2eb16 0x42020224833a2eb1 0x3000000023e7e738 0x03000000023e7e73

def z719 : W := mkw 0x4d74a0003adf8000 0x04d74a0003adf800 0x7e67e0003fffc00b 0xa7e67e0003fffc00

def z720 : W := mkw 0x8ddfc5b7c0000000 0x08ddfc5b7c000000 0x81e7e7f8c0000001 0x081e7e7f8c000000

def z721 : W := mkw 0x8fdfddb7c0490000 0x08fdfddb7c049000 0x9fffffffc019c007 0xf9fffffffc019c00

def z722 : W := mkw 0x8f54db72c1696944 0x88f54db72c169694 0x5e64e838c3f9f9c8 0x85e64e838c3f9f9c

def z723 : W := mkw 0x3d74036abbb42aa7 0x03d74036abbb42aa 0x91fc07ffc3fe01f3 0x091fc07ffc3fe01f

def z724 : W := mkw 0x9fdfddb7c40014a9 0x09fdfddb7c40014a 0xdfffffffc0183fff 0xfdfffffffc0183ff

def z725 : W := mkw 0x4dfea0083adf8212 0x44dfea0083adf821 0x7fffe0003fffc63b 0xe7fffe0003fffc63

def z726 : W := mkw 0x2b417d7454a2dd18 0x42b417d7454a2dd1 0x5f87f1c4dce7d932 0x55f87f1c4dce7d93

def z727 : W := mkw 0x8bcbddb7c0000000 0x08bcbddb7c000000 0x81e3f7fb00000001 0x181e3f7fb0000000

def z728 : W := mkw 0x9fdfddb7cc5d55e9 0x89fdfddb7cc5d55e 0xfffffffffc1fffff 0xffffffffffc1ffff

def z729 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe00ff83fe0260d 0xaafe00ff83fe0260

def z730 : W := mkw 0x8f55ddb7c0000000 0x08f55ddb7c000000 0x8e67ffffc0000007 0xb8e67ffffc000000

def z731 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe01ff83fe03e05 0x9afe01ff83fe03e0

def z732 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7f9c1807fffe3fff 0xf7f9c1807fffe3ff

def z733 : W := mkw 0x8fdfddb7c0004100 0x08fdfddb7c000410 0x9fffffffc001c107 0xf9fffffffc001c10

def z734 : W := mkw 0x32015f7ec5207fbf 0x432015f7ec5207fb 0x80001fffc0003ff4 0x180001fffc0003ff

def z735 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e3e7fc00000007 0x281e3e7fc0000000

def z736 : W := mkw 0x6b60bb6837a2be0e 0x06b60bb6837a2be0 0xefe0fff83fe03e0d 0xfefe0fff83fe03e0

def z737 : W := mkw 0xa4bfc6dff7a03e0e 0x0a4bfc6dff7a03e0 0x601fe007ffe03e0a 0x0601fe007ffe03e0

def z738 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e1c1807fc1e3ff4 0xd6e1c1807fc1e3ff

def z739 : W := mkw 0x008b06cd01696b56 0xc008b06cd01696b5 0xd19b17c703f9ffff 0x7d19b17c703f9fff

def z740 : W := mkw 0x82015db7c0000000 0x082015db7c000000 0x8064ffffc0000004 0x98064ffffc000000

def z741 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xf19f17c723fff9cf 0xff19f17c723fff9c

def z742 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffff7fb00000003 0xf8ffff7fb0000000

def z743 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb07fee3fe31fe7ff 0xab07fee3fe31fe7f

def z744 : W := mkw 0x169f1ec78d7d7ded 0x8169f1ec78d7d7de 0xaf870fc0ffe7c631 0x8af870fc0ffe7c63

def z745 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xcfffffffc3e0000f 0xfcfffffffc3e0000

def z746 : W := mkw 0x8bcbddb7c0000000 0x08bcbddb7c000000 0x81e3eff8c0000001 0x081e3eff8c000000

def z747 : W := mkw 0x302022483fb6ffbf 0x4302022483fb6ffb 0x700000003ffffff8 0x0700000003ffffff

def z748 : W := mkw 0x002022482322eb56 0xc002022482322eb5 0x300000002307fff8 0x0300000002307fff

def z749 : W := mkw 0x202022482722ff1e 0x4202022482722ff1 0x300000002307ff38 0x0300000002307ff3

def z750 : W := mkw 0x8ddfc5b7c0000000 0x08ddfc5b7c000000 0x81fff7ffc0000007 0x781fff7ffc000000

def z751 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff807ffffffff 0xf7ffff807fffffff

def z752 : W := mkw 0x828b5db7c0000000 0x0828b5db7c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z753 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0xb1e7effce006273f 0xab1e7effce006273

def z754 : W := mkw 0x9fdfddb7cc5d14a9 0x09fdfddb7cc5d14a 0xffffffffffffffff 0xffffffffffffffff

def z755 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xfff81ffffff83fff 0xffff81ffffff83ff

def z756 : W := mkw 0xdfde99a39cdd14a9 0x0dfde99a39cdd14a 0x4f9811c31cf818c0 0x54f9811c31cf818c

def z757 : W := mkw 0xdfdfddb7dcdd14a9 0x0dfdfddb7dcdd14a 0xfffffffffcfe3fff 0xffffffffffcfe3ff

def z758 : W := mkw 0x0941453440000000 0x0094145344000000 0x81e7effcc0000007 0xa81e7effcc000000

def z759 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19b17c303f9d8cb 0x7d19b17c303f9d8c

def z760 : W := mkw 0xc49fe495485f8000 0x0c49fe495485f800 0x101fe000001fc002 0x0101fe000001fc00

def z761 : W := mkw 0x9fdfddb7c81400a1 0x09fdfddb7c81400a 0xfffffffffc1e01ff 0xffffffffffc1e01f

def z762 : W := mkw 0x2b603b6837a2ff1e 0x42b603b6837a2ff1 0xffe7fff83fe7ff3f 0xfffe7fff83fe7ff3

def z763 : W := mkw 0x2020224837a2be0e 0x02020224837a2be0 0x700000003fe7fe08 0x0700000003fe7fe0

def z764 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fffeff8c0000003 0xe8fffeff8c000000

def z765 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xa067ee3ce307e735 0x8a067ee3ce307e73

def z766 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xa067ee3ce307c637 0xaa067ee3ce307c63

def z767 : W := mkw 0x99cbc5b54c1414a9 0x099cbc5b54c1414a 0xf1e3e7f83c1e3ff9 0x0f1e3e7f83c1e3ff

def z768 : W := mkw 0x0d7420003a968000 0x00d7420003a96800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z769 : W := mkw 0x0bca992000000000 0x00bca99200000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z770 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xc19b17c303f9f8cd 0x7c19b17c303f9f8c

def z771 : W := mkw 0x92015db7c40014a9 0x092015db7c40014a 0xb067ffffe0063fff 0xbb067ffffe0063ff

def z772 : W := mkw 0xcfdfddb7d8940000 0x0cfdfddb7d894000 0x8fffffffdc000007 0xf8fffffffdc00000

def z773 : W := mkw 0x602022483fffff1e 0x4602022483fffff1 0x700000003fffff38 0x0700000003fffff3

def z774 : W := mkw 0x008b46d541696954 0xc008b46d54169695 0xd19b17c7c3f9f9ff 0x7d19b17c7c3f9f9f

def z775 : W := mkw 0x4ddfc61c59dd6316 0x44ddfc61c59dd631 0xcf980e3cdcf82734 0x4cf980e3cdcf8273

def z776 : W := mkw 0x8bcbddb7c0000000 0x08bcbddb7c000000 0x81fbffffc0000007 0x781fbffffc000000

def z777 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e3f7f800000005 0x781e3f7f80000000

def z778 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb067ee3ce007e736 0x8b067ee3ce007e73

def z779 : W := mkw 0x0021669d6302e316 0x40021669d6302e31 0xb067ffffe307e73f 0xbb067ffffe307e73

def z780 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x4fe3e0001fe1c001 0x44fe3e0001fe1c00

def z781 : W := mkw 0x0b40192010800000 0x00b4019201080000 0xcfe01ff81ce00005 0xfcfe01ff81ce0000

def z782 : W := mkw 0x9f54d932cc1414a9 0x09f54d932cc1414a 0xefe4fff8fc063e3d 0xfefe4fff8fc063e3

def z783 : W := mkw 0x9fdfddb7c81400a1 0x09fdfddb7c81400a 0xdfffffffc01e39ff 0xfdfffffffc01e39f

def z784 : W := mkw 0x0000024001696944 0x8000002400169694 0xd19817c703f9f9cf 0x7d19817c703f9f9c

def z785 : W := mkw 0x008b04c500690840 0x8008b04c50069084 0xd19b17c703f9d8cf 0x7d19b17c703f9d8c

def z786 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xfffffffffc1e063f 0xffffffffffc1e063

def z787 : W := mkw 0x49eaa0003adf8000 0x049eaa0003adf800 0x7fe3e0003fffc009 0xe7fe3e0003fffc00

def z788 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe017f83fe01809 0xfefe017f83fe0180

def z789 : W := mkw 0x8ddfc5b7c0000000 0x08ddfc5b7c000000 0x81ffefffc0000007 0xa81ffefffc000000

def z790 : W := mkw 0x00202248236beb56 0xc00202248236beb5 0x3000000023e7e738 0x03000000023e7e73

def z791 : W := mkw 0x2b601b6837a07f4e 0x82b601b6837a07f4 0xefe01ff83fe03fcd 0xfefe01ff83fe03fc

def z792 : W := mkw 0x2b401b6815a03e0e 0x02b401b6815a03e0 0xcf8017f81ce01800 0x5cf8017f81ce0180

def z793 : W := mkw 0x669ebb680d7fbe0e 0x0669ebb680d7fbe0 0x901ffff8001ffe06 0x1901ffff8001ffe0

def z794 : W := mkw 0x29eb67fd73ebeb56 0xc29eb67fd73ebeb5 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z795 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe004ffffc13b 0xe7fffe004ffffc13

def z796 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7f9fe0003fffc00a 0x47f9fe0003fffc00

def z797 : W := mkw 0x9fdfddb7c40014a9 0x09fdfddb7c40014a 0xeffffffffc003fff 0xfeffffffffc003ff

def z798 : W := mkw 0x2b603b6837a2be0e 0x02b603b6837a2be0 0xefe4fff83fe63e0d 0xfefe4fff83fe63e0

def z799 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x5fffe0001fffc003 0x45fffe0001fffc00

def z800 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xfff81ff83ff83e0f 0xffff81ff83ff83e0

def z801 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8e7fffffc0000006 0x98e7fffffc000000

def z802 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6fffe0003fffc001 0xc6fffe0003fffc00

def z803 : W := mkw 0xcdfea1a13adf8000 0x0cdfea1a13adf800 0x7fffe1c03fffc00b 0xe7fffe1c03fffc00

def z804 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe0033fffc0cb 0xe7fffe0033fffc0c

def z805 : W := mkw 0x0020601862028212 0x4002060186202821 0x2067e838e307c631 0x82067e838e307c63

def z806 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xefe017f83fe0380d 0xfefe017f83fe0380

def z807 : W := mkw 0x2b601b6ab7a03e0e 0x02b601b6ab7a03e0 0xefe01fffffe03e0d 0xfefe01fffffe03e0

def z808 : W := mkw 0x44bea0003adf8000 0x044bea0003adf800 0x7e1fe0003fffc00a 0xe7e1fe0003fffc00

def z809 : W := mkw 0x0020601862028212 0x4002060186202821 0x3067e838e007c632 0x83067e838e007c63

def z810 : W := mkw 0x02201a4827203e0e 0x002201a4827203e0 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z811 : W := mkw 0x2020224837a2be1e 0x42020224837a2be1 0x600000003fe63e38 0x0600000003fe63e3

def z812 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19b17c303f9f9c9 0x5d19b17c303f9f9c

def z813 : W := mkw 0x0b40192000000000 0x00b4019200000000 0x8fe7fff800000007 0xf8fe7fff80000000

def z814 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0xfffff7c03fffc00f 0xffffff7c03fffc00

def z815 : W := mkw 0x000164144002c110 0x4000164144002c11 0xb067ee3ce007e73f 0xab067ee3ce007e73

def z816 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe41ff8ffe63e3d 0xfefe41ff8ffe63e3

def z817 : W := mkw 0x0021641c6202c312 0x40021641c6202c31 0x2067e838e007c630 0x82067e838e007c63

def z818 : W := mkw 0x2b401b6815a03e0e 0x02b401b6815a03e0 0xcfe01ff81ce03e05 0xfcfe01ff81ce03e0

def z819 : W := mkw 0x2beb1dad36c9574a 0x82beb1dad36c9574 0x3e7b083f3c19c7c2 0x83e7b083f3c19c7c

def z820 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x8fe3e7f800000001 0xe8fe3e7f80000000

def z821 : W := mkw 0x0200180004001408 0x0020018000400140 0x7e1c1807fc1e3ffe 0xf7e1c1807fc1e3ff

def z822 : W := mkw 0x0b40593040000000 0x00b4059304000000 0x8fe4fff8c0000005 0xf8fe4fff8c000000

def z823 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01fff3fe03fcd 0xfefe01fff3fe03fc

def z824 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xbffffffffc06273f 0xfbffffffffc06273

def z825 : W := mkw 0x8fdfddb7c0490000 0x08fdfddb7c049000 0xdfffffffc3f9f9cf 0xfdfffffffc3f9f9c

def z826 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xdfffffffdc1e19f7 0xfdfffffffdc1e19f

def z827 : W := mkw 0xcfdfddb7c85d0000 0x0cfdfddb7c85d000 0x8fffffffc0180007 0xf8fffffffc018000

def z828 : W := mkw 0x8fdfddb7c0004110 0x48fdfddb7c000411 0x8fffffffc0000137 0xf8fffffffc000013

def z829 : W := mkw 0x008a02c101696944 0x8008a02c10169694 0x519b11c303f9f9cb 0x7519b11c303f9f9c

def z830 : W := mkw 0x002062186302e316 0x4002062186302e31 0x3067e838e307e73b 0xa3067e838e307e73

def z831 : W := mkw 0x8b415db7c0000000 0x08b415db7c000000 0x8fe7ffffc0000007 0xf8fe7ffffc000000

def z832 : W := mkw 0xc49fc497c85d0000 0x0c49fc497c85d000 0x001fe007c0180002 0x0001fe007c018000

def z833 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe01ff83fe63f3d 0xfffe01ff83fe63f3

def z834 : W := mkw 0x8fdfddb7c4001408 0x08fdfddb7c400140 0xfffffffffc063f3f 0xffffffffffc063f3

def z835 : W := mkw 0x0fdfdd3440000000 0x00fdfdd344000000 0x8ffffffcc0000007 0xf8ffffffcc000000

def z836 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c0807fc1e3ffa 0x87e1c0807fc1e3ff

def z837 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81ffffffc0000007 0xf81ffffffc000000

def z838 : W := mkw 0x8ffebbaba302e316 0x48ffebbaba302e31 0x3f9811c32307e738 0x53f9811c32307e73

def z839 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb067ee3ce307c733 0x8b067ee3ce307c73

def z840 : W := mkw 0x8fdfddb7c4001408 0x08fdfddb7c400140 0xfffffffffc183fcf 0xffffffffffc183fc

def z841 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7ffff007fffff9ff 0xf7ffff007fffff9f

def z842 : W := mkw 0x008b449540000000 0x0008b44954000000 0xf1ffffffe01e3fff 0xff1ffffffe01e3ff

def z843 : W := mkw 0x16357e1eef16f7bf 0x416357e1eef16f7b 0xce7bf63b1f19d8c1 0x5ce7bf63b1f19d8c

def z844 : W := mkw 0x008b048500490000 0x0008b04850049000 0xd19b17c703f9f9cf 0x7d19b17c703f9f9c

def z845 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ff83fe01e01 0xdefe01ff83fe01e0

def z846 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xbfffffffe006000f 0xfbfffffffe006000

def z847 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x7fe7e0003fe7c00b 0xe7fe7e0003fe7c00

def z848 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe00ff83fe00609 0xeefe00ff83fe0060

def z849 : W := mkw 0x8bcbddb540000000 0x08bcbddb54000000 0x81e3fff800000005 0x181e3fff80000000

def z850 : W := mkw 0x5beab802b6cb94a9 0x05beab802b6cb94a 0x01e3f807c3e1fff5 0x101e3f807c3e1fff

def z851 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81e3e7f800000001 0x081e3e7f80000000

def z852 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffbffffc0000005 0x58ffbffffc000000

def z853 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0x3067e83ce307e73a 0x83067e83ce307e73

def z854 : W := mkw 0x0fde99200c141408 0x00fde99200c14140 0xfffffff83c1e3e0f 0xffffffff83c1e3e0

def z855 : W := mkw 0x2b401b6815a03e0e 0x02b401b6815a03e0 0xcf801ff81fe03e0d 0x7cf801ff81fe03e0

def z856 : W := mkw 0x2b603b6837a2be0e 0x02b603b6837a2be0 0xffe01ff83fe7fe0d 0xfffe01ff83fe7fe0

def z857 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb067ee38e307c63b 0xab067ee38e307c63

def z858 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb067ee38e307e739 0x8b067ee38e307e73

def z859 : W := mkw 0x008a00c100690840 0x8008a00c10069084 0x519b11c703f9f9cf 0x7519b11c703f9f9c

def z860 : W := mkw 0x2b6019283680160a 0x02b6019283680160 0xefe01ff83fe0060d 0xfefe01ff83fe0060

def z861 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xdfffffffc018000f 0xfdfffffffc018000

def z862 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xefe00ff83fe0260d 0xeefe00ff83fe0260

def z863 : W := mkw 0x1f555d36cc1414a9 0x01f555d36cc1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z864 : W := mkw 0x8fdfddb540000000 0x08fdfddb54000000 0x8ffffff800000007 0xf8ffffff80000000

def z865 : W := mkw 0x949fc497c85d41e1 0x8949fc497c85d41e 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z866 : W := mkw 0x00202248236beb56 0xc00202248236beb5 0x701c1807e3fffffe 0xf701c1807e3fffff

def z867 : W := mkw 0x9fdfddb7c81400a1 0x09fdfddb7c81400a 0xbfffffffe01e27ff 0xfbfffffffe01e27f

def z868 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e181807fc1e3ffc 0x57e181807fc1e3ff

def z869 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ff83ce03e04 0xdefe01ff83ce03e0

def z870 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe7fff83fe03e0f 0xfefe7fff83fe03e0

def z871 : W := mkw 0x0f54992000000000 0x00f5499200000000 0x8fe4fff800000005 0xf8fe4fff80000000

def z872 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xeffffffffc063e3f 0xfeffffffffc063e3

def z873 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81fbe7f800000003 0x681fbe7f80000000

def z874 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0033fffd8cb 0xf7ffff0033fffd8c

def z875 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xeffffffffc183ecf 0xfeffffffffc183ec

def z876 : W := mkw 0x09ca812000000000 0x009ca81200000000 0x81e3e7f800000001 0x081e3e7f80000000

def z877 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fffffffc0002737 0xf8fffffffc000273

def z878 : W := mkw 0x008b46dd41696b56 0xc008b46dd41696b5 0xf19f1fffe3ffffff 0xff19f1fffe3fffff

def z879 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x8fe007f81fe00001 0x08fe007f81fe0000

def z880 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x2fe3e0003fe1c001 0x82fe3e0003fe1c00

def z881 : W := mkw 0x8bcbddb544001408 0x08bcbddb54400140 0xefe3fff83c003e0d 0xfefe3fff83c003e0

def z882 : W := mkw 0x443420003adf8000 0x0443420003adf800 0x7e7fe0003fffc00b 0xe7e7fe0003fffc00

def z883 : W := mkw 0xc2217db7fadf8000 0x0c2217db7fadf800 0xf0001fffffffc00c 0x1f0001fffffffc00

def z884 : W := mkw 0x0f555d36c0000000 0x00f555d36c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z885 : W := mkw 0x36343a4abfb6ffbf 0x436343a4abfb6ffb 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z886 : W := mkw 0x8fdfddb7c85d0000 0x08fdfddb7c85d000 0xffffffffffffc00f 0xfffffffffffffc00

def z887 : W := mkw 0x8bcbddb7c0000000 0x08bcbddb7c000000 0x8fe3ffffc0000005 0xf8fe3ffffc000000

def z888 : W := mkw 0xcfdfddb7d8dd0000 0x0cfdfddb7d8dd000 0xfffffffffcfe000f 0xffffffffffcfe000

def z889 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e7e7fcc0000003 0x081e7e7fcc000000

def z890 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xf1e7ee3ce3e7e73f 0xef1e7ee3ce3e7e73

def z891 : W := mkw 0x0960012032800000 0x0096001203280000 0xefe007f83fe00009 0xeefe007f83fe0000

def z892 : W := mkw 0x8fdfddb7c8140000 0x08fdfddb7c814000 0xfffffffffc1e39cf 0xffffffffffc1e39c

def z893 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd1fb1fff03f9f9cf 0xfd1fb1fff03f9f9c

def z894 : W := mkw 0x66343a483fffbe0e 0x066343a483fffbe0 0x7e1c18003ffffe0e 0xf7e1c18003ffffe0

def z895 : W := mkw 0x0001661c4102e316 0x40001661c4102e31 0x9067ee3cc007e737 0xa9067ee3cc007e73

def z896 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x9fffffffc000210f 0xf9fffffffc000210

def z897 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x7ffbe0003ff9c00b 0xe7ffbe0003ff9c00

def z898 : W := mkw 0x92015ff7c5207ded 0x892015ff7c5207de 0x80001fffc0003ff4 0x180001fffc0003ff

def z899 : W := mkw 0x00202248236beb56 0xc00202248236beb5 0x5000000003f9f9c8 0x05000000003f9f9c

def z900 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x3fffe0003fffc003 0x83fffe0003fffc00

def z901 : W := mkw 0x0021665c6322eb16 0x40021665c6322eb1 0xb067fffce307ff3f 0xbb067fffce307ff3

def z902 : W := mkw 0x2b601b6837a07f0e 0x02b601b6837a07f0 0xffe01ff83fe1ff0d 0xfffe01ff83fe1ff0

def z903 : W := mkw 0x4dfea0813adf8040 0x84dfea0813adf804 0x7fffe0033fffc0cb 0xe7fffe0033fffc0c

def z904 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xafe7eff8fc060631 0x8afe7eff8fc06063

def z905 : W := mkw 0x4dfea0083adf8202 0x04dfea0083adf820 0x7fffe8383fffc60b 0xe7fffe8383fffc60

def z906 : W := mkw 0x00aa60d9626b8a52 0xc00aa60d9626b8a5 0x61fcf9fbe0fe1ef0 0xd61fcf9fbe0fe1ef

def z907 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xbffffffffc1e07f7 0xfbffffffffc1e07f

def z908 : W := mkw 0x6020224833ebaa06 0x06020224833ebaa0 0x0000000003e1c000 0x00000000003e1c00

def z909 : W := mkw 0x8fdfddb7cc141408 0x08fdfddb7cc14140 0xfffffffffc1e3e0f 0xffffffffffc1e3e0

def z910 : W := mkw 0xdfdfddb7dcdd14a9 0x0dfdfddb7dcdd14a 0xcfffffffdcf818c7 0xfcfffffffdcf818c

def z911 : W := mkw 0x3f74793afe9696bb 0x43f74793afe9696b 0x2e64e838fc060630 0x82e64e838fc06063

def z912 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fe7ffffc0000005 0x98fe7ffffc000000

def z913 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0073fffc00f 0xf7ffff0073fffc00

def z914 : W := mkw 0x8ddfc5b548140000 0x08ddfc5b54814000 0xffffe7f83c1e000b 0xeffffe7f83c1e000

def z915 : W := mkw 0x8f55ddb7c0000000 0x08f55ddb7c000000 0x8e64eff8c0000000 0x88e64eff8c000000

def z916 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe31ff83fe1fe0f 0xfffe31ff83fe1fe0

def z917 : W := mkw 0x2b601b6837a07f1e 0x42b601b6837a07f1 0xefe01ff83fe03f3d 0xfefe01ff83fe03f3

def z918 : W := mkw 0x8f54d932c0000000 0x08f54d932c000000 0x8fe4eff8c0000001 0x88fe4eff8c000000

def z919 : W := mkw 0x0021641c62028212 0x40021641c6202821 0xb067ee3ce307c63f 0xab067ee3ce307c63

def z920 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xeffffffffc00000f 0xfeffffffffc00000

def z921 : W := mkw 0x02015d3440000000 0x002015d344000000 0x8067fffcc0000007 0xb8067fffcc000000

def z922 : W := mkw 0x008b46dd41696b56 0xc008b46dd41696b5 0xd19b17ff03f9f9cf 0x7d19b17ff03f9f9c

def z923 : W := mkw 0x002022082302a206 0x0002022082302a20 0xb067ee3ce307e73f 0xab067ee3ce307e73

def z924 : W := mkw 0x8b41ddb7c0000000 0x08b41ddb7c000000 0x8060ffffc0000004 0x18060ffffc000000

def z925 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7e7fe0003fffc00a 0x87e7fe0003fffc00

def z926 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0x9fffffffc01e3ff7 0xf9fffffffc01e3ff

def z927 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x9fffffffc301c00f 0xf9fffffffc301c00

def z928 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe017f83fe03e09 0x5efe017f83fe03e0

def z929 : W := mkw 0x2b40196014a01c08 0x02b40196014a01c0 0xefe01ff83ce03e0d 0xfefe01ff83ce03e0

def z930 : W := mkw 0x89cbc5b7c0000000 0x089cbc5b7c000000 0x81e3e7ffc0000001 0x081e3e7ffc000000

def z931 : W := mkw 0x0bcb5db540000000 0x00bcb5db54000000 0x8fffffffc0000007 0xf8fffffffc000000

def z932 : W := mkw 0x2b603b6837a2ff1e 0x42b603b6837a2ff1 0xefe01ff83fe1fe0d 0xfefe01ff83fe1fe0

def z933 : W := mkw 0x8ddfc5b540000000 0x08ddfc5b54000000 0x8ffbe7f800000001 0x48ffbe7f80000000

def z934 : W := mkw 0x0001449540000000 0x0000144954000000 0x8067ffffc0000007 0xb8067ffffc000000

def z935 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z936 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xcfffffffc000380f 0xfcfffffffc000380

def z937 : W := mkw 0x2960036837a03e0e 0x02960036837a03e0 0xefe007f83fe03e09 0xeefe007f83fe03e0

def z938 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e7e7f800000003 0xa81e7e7f80000000

def z939 : W := mkw 0x8f55ddb7c0000000 0x08f55ddb7c000000 0x8e7cffffc0000006 0xf8e7cffffc000000

def z940 : W := mkw 0x22015f7c45207f1e 0x422015f7c45207f1 0x80001ff800003e04 0x180001ff800003e0

def z941 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0003ffff80f 0xf7ffff0003ffff80

def z942 : W := mkw 0x402022483bffeb56 0xc402022483bffeb5 0x700000003ffffff8 0x0700000003ffffff

def z943 : W := mkw 0x8ddfc5b7c0000000 0x08ddfc5b7c000000 0x8fffe7ffc0000003 0xe8fffe7ffc000000

def z944 : W := mkw 0x4d75a6c53bb6e944 0x84d75a6c53bb6e94 0xae64f7c73c0639c4 0x9ae64f7c73c0639c

def z945 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fe3e7f800000001 0x08fe3e7f80000000

def z946 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe8003fffe60f 0xe7fffe8003fffe60

def z947 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81fbf7ff00000007 0x781fbf7ff0000000

def z948 : W := mkw 0x602022483fffff4e 0x8602022483fffff4 0x700000003fffffc8 0x0700000003fffffc

def z949 : W := mkw 0x8fdfddb7c0494140 0x88fdfddb7c049414 0xdfffffffc019f9cf 0xfdfffffffc019f9c

def z950 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xeffffffffc1e1ef7 0xfeffffffffc1e1ef

def z951 : W := mkw 0x008a024001692804 0x0008a02400169280 0xd19b17c703f9f9cf 0x7d19b17c703f9f9c

def z952 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6fe7e0003fe7c009 0xe6fe7e0003fe7c00

def z953 : W := mkw 0x6dfea1283adf8202 0x06dfea1283adf820 0x7fffe0383fffc00b 0xe7fffe0383fffc00

def z954 : W := mkw 0x9fdfddb7c40014a9 0x09fdfddb7c40014a 0x8fffffffc0000637 0xf8fffffffc000063

def z955 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xf067fe3ce307ff3f 0xff067fe3ce307ff3

def z956 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x81ffffffc0000007 0x181ffffffc000000

def z957 : W := mkw 0x2020224833a2eb16 0x42020224833a2eb1 0x0000000003e1c000 0x00000000003e1c00

def z958 : W := mkw 0xa2015fffc5207f1e 0x4a2015fffc5207f1 0x80001fffc0003f34 0x180001fffc0003f3

def z959 : W := mkw 0x496020003adf8000 0x0496020003adf800 0x7fe7e0003fffc00b 0xe7fe7e0003fffc00

def z960 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xfffffffffc1e18cf 0xffffffffffc1e18c

def z961 : W := mkw 0x8b40d93040000000 0x08b40d9304000000 0x8fe0fff800000005 0xf8fe0fff80000000

def z962 : W := mkw 0x0001461441006104 0x0000146144100610 0xb067ee3ce307e73f 0xab067ee3ce307e73

def z963 : W := mkw 0x76343a4abfffbeaf 0x076343a4abfffbea 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z964 : W := mkw 0xd49fe497c85f80a1 0x0d49fe497c85f80a 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z965 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0x8fffffffdc000007 0xf8fffffffdc00000

def z966 : W := mkw 0xcfdfddb7d8dd0000 0x0cfdfddb7d8dd000 0xdfffffffdff9c00f 0xfdfffffffdff9c00

def z967 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x9fffffffc01801c7 0xf9fffffffc01801c

def z968 : W := mkw 0x22001b6805203e0e 0x022001b6805203e0 0xef801ff83fe03e0d 0xfef801ff83fe03e0

def z969 : W := mkw 0x0021641462028000 0x0002164146202800 0xb067ee3ce307e73f 0xab067ee3ce307e73

def z970 : W := mkw 0x1fde99228c1414a9 0x01fde99228c1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z971 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x7f9fe0003fffc00b 0xe7f9fe0003fffc00

def z972 : W := mkw 0xcddfc5b558dd0000 0x0cddfc5b558dd000 0xcffbe7f81cf80001 0x4cffbe7f81cf8000

def z973 : W := mkw 0x8fdfddb7c4001408 0x08fdfddb7c400140 0xcfffffffdc001807 0xfcfffffffdc00180

def z974 : W := mkw 0x008a02c101692844 0x8008a02c10169284 0xd19b17c303f9f8cf 0x7d19b17c303f9f8c

def z975 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81e7effcc0000007 0xa81e7effcc000000

def z976 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x519b11c703f9f9ca 0x5519b11c703f9f9c

def z977 : W := mkw 0x8fdfddb7c0490040 0x88fdfddb7c049004 0x8fffffffc01800c7 0xf8fffffffc01800c

def z978 : W := mkw 0x00202248236beb56 0xc00202248236beb5 0x0000000003e1c000 0x00000000003e1c00

def z979 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xaffffffffc063ff7 0xfaffffffffc063ff

def z980 : W := mkw 0x008a00c100690840 0x8008a00c10069084 0x419b11c303f9d8c1 0x5419b11c303f9d8c

def z981 : W := mkw 0x9fde99e38c7d1ce9 0x89fde99e38c7d1ce 0x4f9811c31cf818c0 0x54f9811c31cf818c

def z982 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x0fe3e0001fe1c001 0x00fe3e0001fe1c00

def z983 : W := mkw 0xafdfddb7d4801408 0x0afdfddb7d480140 0x8fffffffdc000007 0xf8fffffffdc00000

def z984 : W := mkw 0x8bcbddb540000000 0x08bcbddb54000000 0x8fe3f7f800000001 0x58fe3f7f80000000

def z985 : W := mkw 0x800145b540000000 0x0800145b54000000 0x8063e7f800000001 0x08063e7f80000000

def z986 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xefe01ff8ffe03e3d 0xfefe01ff8ffe03e3

def z987 : W := mkw 0x8fded932c0000000 0x08fded932c000000 0x8ffffff8c0000007 0xf8ffffff8c000000

def z988 : W := mkw 0x8fdfddb7c0004140 0x88fdfddb7c000414 0x8fffffffc00001c7 0xf8fffffffc00001c

def z989 : W := mkw 0x2021665c73a2eb16 0x42021665c73a2eb1 0xb067ee3ce3e7e73f 0xab067ee3ce3e7e73

def z990 : W := mkw 0x04be20002a5f8000 0x004be20002a5f800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z991 : W := mkw 0x8bcbddb7c0000000 0x08bcbddb7c000000 0x81e7ffffc0000007 0xb81e7ffffc000000

def z992 : W := mkw 0x8ddfc5b540000000 0x08ddfc5b54000000 0x8fe7e7f800000001 0x88fe7e7f80000000

def z993 : W := mkw 0x808bc6d541696944 0x8808bc6d54169694 0xd19bf7c703f9f9cf 0x7d19bf7c703f9f9c

def z994 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x5ffbe0001ff9c00b 0x65ffbe0001ff9c00

def z995 : W := mkw 0x9bcbddb7c40014a9 0x09bcbddb7c40014a 0x81e3ffffc0003ff5 0x181e3ffffc0003ff

def z996 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd1fff7c703f9f9cf 0xfd1fff7c703f9f9c

def z997 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe01ff83ff83fcd 0xfffe01ff83ff83fc

def z998 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xff9b17c73ff9f9cf 0xfff9b17c73ff9f9c

def z999 : W := mkw 0x3b601b6837a03eaf 0x03b601b6837a03ea 0xefe01ff83fe03ffd 0xfefe01ff83fe03ff

def z1000 : W := mkw 0x002166dd6322eb56 0xc002166dd6322eb5 0xf1e7ffffe3e7ffff 0xff1e7ffffe3e7fff

def z1001 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6ffbe0003ff9c009 0xe6ffbe0003ff9c00

def z1002 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0x919b17c703f9f9c7 0x1919b17c703f9f9c

def z1003 : W := mkw 0x9fdfddb7c81400a1 0x09fdfddb7c81400a 0x8fffffffc01800c7 0xf8fffffffc01800c

def z1004 : W := mkw 0x8941c5b540000000 0x08941c5b54000000 0x8060e7f800000000 0x08060e7f80000000

def z1005 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0xd1fbf7ff001839cf 0x7d1fbf7ff001839c

def z1006 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xcfffffffc01818c7 0xfcfffffffc01818c

def z1007 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xf07fee3ce31fe73f 0xef07fee3ce31fe73

def z1008 : W := mkw 0x0dde8000085d0000 0x00dde8000085d000 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z1009 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xffffffffe01e3fff 0xfffffffffe01e3ff

def z1010 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe800ffffc63b 0xe7fffe800ffffc63

def z1011 : W := mkw 0x9fdfddb7c85d41e1 0x89fdfddb7c85d41e 0x9fffffffc01fc1f7 0xf9fffffffc01fc1f

def z1012 : W := mkw 0x8bcbddb540000000 0x08bcbddb54000000 0x8fe3eff800000001 0x88fe3eff80000000

def z1013 : W := mkw 0x2020224837a2ff1e 0x42020224837a2ff1 0x600000003fe1fe08 0x0600000003fe1fe0

def z1014 : W := mkw 0x2b60196036a01c08 0x02b60196036a01c0 0xefe01ff83fe0180d 0xfefe01ff83fe0180

def z1015 : W := mkw 0x12015edfc5207fff 0xc12015edfc5207ff 0x80001fffc0003ff4 0x180001fffc0003ff

def z1016 : W := mkw 0xc49fe497c85fc140 0x8c49fe497c85fc14 0x101fe007c01fc1c2 0x0101fe007c01fc1c

def z1017 : W := mkw 0x161419228c1414a9 0x0161419228c1414a 0xfe1c1ffffc1e3ffe 0xffe1c1ffffc1e3ff

def z1018 : W := mkw 0x2b40196014a01c08 0x02b40196014a01c0 0xcf801ff81ce01804 0x5cf801ff81ce0180

def z1019 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xc19b17c703f9d8c7 0x7c19b17c703f9d8c

def z1020 : W := mkw 0x2b603b6837a2be0e 0x02b603b6837a2be0 0xefe3fff83fe1fe0d 0xfefe3fff83fe1fe0

def z1021 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb07ffe3fe307e73f 0xfb07ffe3fe307e73

def z1022 : W := mkw 0x9ddfc5b7c81400a1 0x09ddfc5b7c81400a 0x91ffe7ffc01e01f3 0x091ffe7ffc01e01f

def z1023 : W := mkw 0x2b603b6837a2ff1e 0x42b603b6837a2ff1 0xffe41ffcffe7ff3f 0xfffe41ffcffe7ff3

def z1024 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffffffbc0000001 0xd8ffffffbc000000

def z1025 : W := mkw 0x102022482f7fffff 0xc102022482f7ffff 0x700000003ffffff8 0x0700000003ffffff

def z1026 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe00ff83fe03e09 0x8efe00ff83fe03e0

def z1027 : W := mkw 0x0001441440000000 0x0000144144000000 0x81e7fffcc0000007 0xf81e7fffcc000000

def z1028 : W := mkw 0x702022483fffbeaf 0x0702022483fffbea 0x700000003ffffff8 0x0700000003ffffff

def z1029 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xef801ff83fe03e0c 0x5ef801ff83fe03e0

def z1030 : W := mkw 0x0020601862028212 0x4002060186202821 0x3067e83ce307e73f 0xa3067e83ce307e73

def z1031 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xeff81ffb3ff83ecd 0xfeff81ffb3ff83ec

def z1032 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x3fe7e0003fe7c00b 0xa3fe7e0003fe7c00

def z1033 : W := mkw 0x008a00c100690840 0x8008a00c10069084 0x519811c303f9d8c8 0x5519811c303f9d8c

def z1034 : W := mkw 0x8f55dd36c0000000 0x08f55dd36c000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z1035 : W := mkw 0x8ddfc5b540000000 0x08ddfc5b54000000 0x8fffeffcc0000007 0xe8fffeffcc000000

def z1036 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffbfffb00000005 0xf8ffbfffb0000000

def z1037 : W := mkw 0x22203a4837a2ff1e 0x422203a4837a2ff1 0x7e041804ffe7ff3e 0xf7e041804ffe7ff3

def z1038 : W := mkw 0x82015db7c0000000 0x082015db7c000000 0x8063ffffc0000005 0x18063ffffc000000

def z1039 : W := mkw 0x8ddfc5b540000000 0x08ddfc5b54000000 0x81ffe7f800000003 0x081ffe7f80000000

def z1040 : W := mkw 0x0021665c6322eb16 0x40021665c6322eb1 0xf067ee3ce3e7ff3f 0xaf067ee3ce3e7ff3

def z1041 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1f1807ff1fffff 0xf7e1f1807ff1ffff

def z1042 : W := mkw 0x4dfea00032cb8000 0x04dfea00032cb800 0x6fffe0003fe1c00b 0xe6fffe0003fe1c00

def z1043 : W := mkw 0x4dfea002badf8000 0x04dfea002badf800 0x7fffe007ffffc00b 0xe7fffe007ffffc00

def z1044 : W := mkw 0x008b46d541696944 0x8008b46d54169694 0xd1fbf7ff03f9f9cf 0x7d1fbf7ff03f9f9c

def z1045 : W := mkw 0x89cbc5b540490000 0x089cbc5b54049000 0xd1fbe7f803f9c00b 0x6d1fbe7f803f9c00

def z1046 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19b1fc7c3f9ffff 0x7d19b1fc7c3f9fff

def z1047 : W := mkw 0x0dfea00032828000 0x00dfea0003282800 0x7fffe0003fe7c00b 0xe7fffe0003fe7c00

def z1048 : W := mkw 0x2b40196014a01c08 0x02b40196014a01c0 0xcfe017f81ce01801 0x5cfe017f81ce0180

def z1049 : W := mkw 0x169f5c97cc1414a9 0x0169f5c97cc1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z1050 : W := mkw 0x86155db7c0000000 0x086155db7c000000 0x8e7fffffc0000007 0xf8e7fffffc000000

def z1051 : W := mkw 0x49ebe6dd73ebeb56 0xc49ebe6dd73ebeb5 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z1052 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19b17c703f9d9c3 0x5d19b17c703f9d9c

def z1053 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe01ff81fe01805 0xfcfe01ff81fe0180

def z1054 : W := mkw 0x9f55ddb7cc1414a9 0x09f55ddb7cc1414a 0xfe7cfffffc1e3ffe 0xffe7cfffffc1e3ff

def z1055 : W := mkw 0x0b601b6033a02804 0x00b601b6033a0280 0xefe01ff83fe0380d 0xfefe01ff83fe0380

def z1056 : W := mkw 0x002022482322eb16 0x4002022482322eb1 0x7000000023e7ff38 0x07000000023e7ff3

def z1057 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0073fffc1cb 0xe7fffe0073fffc1c

def z1058 : W := mkw 0x8fdfddb7d0800000 0x08fdfddb7d080000 0xcfffffffdce00007 0xfcfffffffdce0000

def z1059 : W := mkw 0x0b401b6005203c0c 0x00b401b6005203c0 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z1060 : W := mkw 0x22015ffd45207f5e 0xc22015ffd45207f5 0x80001fffc0003ff4 0x180001fffc0003ff

def z1061 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xc19b17c703f9f9c5 0x5c19b17c703f9f9c

def z1062 : W := mkw 0x602022483fb6be0e 0x0602022483fb6be0 0x600000003fe63e08 0x0600000003fe63e0

def z1063 : W := mkw 0x9fdfddb7c00000a1 0x09fdfddb7c00000a 0x8fffffffc00001f7 0xf8fffffffc00001f

def z1064 : W := mkw 0x869fddb7c0000000 0x0869fddb7c000000 0x807fffffc0000007 0xb807fffffc000000

def z1065 : W := mkw 0x8f54d932c0000000 0x08f54d932c000000 0x8ffcffffc0000007 0xf8ffcffffc000000

def z1066 : W := mkw 0x008b46d541696944 0x8008b46d54169694 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z1067 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0xffffee383fffc00f 0xeffffee383fffc00

def z1068 : W := mkw 0x0b415d3440000000 0x00b415d344000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z1069 : W := mkw 0x8ddfc5b7c0000000 0x08ddfc5b7c000000 0x81fbe7fb00000001 0x081fbe7fb0000000

def z1070 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e7ff807fc1e3fff 0xf7e7ff807fc1e3ff

def z1071 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe000ffffc03b 0xe7fffe000ffffc03

def z1072 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xafe007f83fe00001 0x8afe007f83fe0000

def z1073 : W := mkw 0x069f5c97c0000000 0x0069f5c97c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1074 : W := mkw 0x09ea200032cb8000 0x009ea200032cb800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z1075 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c1807fc1e3ffe 0xf7e1c1807fc1e3ff

def z1076 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xefe01ffb3fe03ecd 0xfefe01ffb3fe03ec

def z1077 : W := mkw 0x149f6497c85fc1f1 0xc149f6497c85fc1f 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z1078 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fe7fff8c0000005 0xf8fe7fff8c000000

def z1079 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19f1fc7c3f9f9cf 0xfd19f1fc7c3f9f9c

def z1080 : W := mkw 0x0b60192036801408 0x00b6019203680140 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z1081 : W := mkw 0x0960200032828000 0x0096020003282800 0x6fe3e0003fe1c009 0xe6fe3e0003fe1c00

def z1082 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z1083 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe01ff83fe00605 0xfafe01ff83fe0060

def z1084 : W := mkw 0x5dfea0003adf80a1 0x05dfea0003adf80a 0x7fffe0003fffc1fb 0xe7fffe0003fffc1f

def z1085 : W := mkw 0x4dfea0813adf8000 0x04dfea0813adf800 0x7ffff1c33fffc00b 0xf7ffff1c33fffc00

def z1086 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffff7ffc0000003 0x58ffff7ffc000000

def z1087 : W := mkw 0x0dfe800032c90000 0x00dfe800032c9000 0x7fffe0003ff9c00b 0xe7fffe0003ff9c00

def z1088 : W := mkw 0x89cbc5b540494140 0x889cbc5b54049414 0x91fbe7ff0019c1c3 0x091fbe7ff0019c1c

def z1089 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x9fffffffc0060137 0xf9fffffffc006013

def z1090 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x4fffe0001ff9c003 0xe4fffe0001ff9c00

def z1091 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xfe67ee3cff07e73f 0xefe67ee3cff07e73

def z1092 : W := mkw 0x449fe495485fc150 0xc449fe495485fc15 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z1093 : W := mkw 0x16343a4aaf7fffff 0xc16343a4aaf7ffff 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z1094 : W := mkw 0x8fdfddb7c0490000 0x08fdfddb7c049000 0xcfffffffc0f80007 0xfcfffffffc0f8000

def z1095 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0xfe7c1e3ffc1e3fff 0xffe7c1e3ffc1e3ff

def z1096 : W := mkw 0x0fdf9da500000000 0x00fdf9da50000000 0x8fffffff00000007 0xf8fffffff0000000

def z1097 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffbf7ff00000007 0x78ffbf7ff0000000

def z1098 : W := mkw 0x8fdfddb7c8140000 0x08fdfddb7c814000 0xfffffffffc1e273f 0xffffffffffc1e273

def z1099 : W := mkw 0x4dfea1203adf8000 0x04dfea1203adf800 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z1100 : W := mkw 0x9f55ddb7cc1414a9 0x09f55ddb7cc1414a 0xae64fffffc063ff4 0x9ae64fffffc063ff

def z1101 : W := mkw 0x0fde992280000000 0x00fde99228000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1102 : W := mkw 0x008b46dd41696b56 0xc008b46dd41696b5 0xd1ffffffc3f9ffff 0xfd1ffffffc3f9fff

def z1103 : W := mkw 0x008a02c101696944 0x8008a02c10169694 0xd19817c303f9f9cd 0x7d19817c303f9f9c

def z1104 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe41ffcffe03e0f 0xfefe41ffcffe03e0

def z1105 : W := mkw 0x8f54d932c0000000 0x08f54d932c000000 0x8e64fff8c0000004 0x98e64fff8c000000

def z1106 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81fbf7fb00000001 0x581fbf7fb0000000

def z1107 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe804ffffc00f 0xe7fffe804ffffc00

def z1108 : W := mkw 0x9fdfddb7c40014a9 0x09fdfddb7c40014a 0xbfffffffe0063fff 0xfbfffffffe0063ff

def z1109 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19817c703f9f9cc 0x5d19817c703f9f9c

def z1110 : W := mkw 0x002166dd6322eb56 0xc002166dd6322eb5 0xf07fffffe31fffff 0xff07fffffe31ffff

def z1111 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xcfe007f81fe00001 0x4cfe007f81fe0000

def z1112 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb1e7fffce307e73f 0xfb1e7fffce307e73

def z1113 : W := mkw 0x8fded9b3c0000000 0x08fded9b3c000000 0x8ffcfffbc0000005 0xf8ffcfffbc000000

def z1114 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe01ffc3fe03f0f 0xfffe01ffc3fe03f0

def z1115 : W := mkw 0x2b60196836a01e0a 0x02b60196836a01e0 0xefe01ff83ce01e05 0xfefe01ff83ce01e0

def z1116 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fffefffc0000003 0x88fffefffc000000

def z1117 : W := mkw 0x7f74b92abe9696ab 0x07f74b92abe9696a 0x2e64e838fc060630 0x82e64e838fc06063

def z1118 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xfffc1ffffffe3fff 0xffffc1ffffffe3ff

def z1119 : W := mkw 0x008a02c101696944 0x8008a02c10169694 0x519811c703f9f9ce 0x7519811c703f9f9c

def z1120 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xcffbf7fb1c1818c1 0x5cffbf7fb1c1818c

def z1121 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xcfffffffdc183ff7 0xfcfffffffdc183ff

def z1122 : W := mkw 0x7fde99629cfd1ca9 0x07fde99629cfd1ca 0x4f9811c31cf818c0 0x54f9811c31cf818c

def z1123 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xf19b1fc723f9ffcf 0xff19b1fc723f9ffc

def z1124 : W := mkw 0x9fdfddb7c81400a1 0x09fdfddb7c81400a 0x8fffffffc0060037 0xf8fffffffc006003

def z1125 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0xff9c1fc7fc1e3fff 0xfff9c1fc7fc1e3ff

def z1126 : W := mkw 0x602022483bffaa06 0x0602022483bffaa0 0x700000003fffc008 0x0700000003fffc00

def z1127 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe017f81fe0380d 0x7cfe017f81fe0380

def z1128 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e3f7ff00000005 0x181e3f7ff0000000

def z1129 : W := mkw 0x8940c13040000000 0x08940c1304000000 0x81e0e7f800000001 0x081e0e7f80000000

def z1130 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xafffffffe000260f 0xfafffffffe000260

def z1131 : W := mkw 0x8fde99a380000000 0x08fde99a38000000 0x8ffffffb00000007 0xf8ffffffb0000000

def z1132 : W := mkw 0x9fdfddb7cc1414a9 0x09fdfddb7cc1414a 0xdfffffffdc1839cf 0xfdfffffffdc1839c

def z1133 : W := mkw 0x8fdfddb7c0494140 0x88fdfddb7c049414 0x8fffffffc001c007 0xf8fffffffc001c00

def z1134 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z1135 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e3effcc0000005 0x081e3effcc000000

def z1136 : W := mkw 0x8ddfc5b540000000 0x08ddfc5b54000000 0x8ffff7ff00000007 0xf8ffff7ff0000000

def z1137 : W := mkw 0x0dde812000000000 0x00dde81200000000 0x8fffe7f800000003 0xe8fffe7f80000000

def z1138 : W := mkw 0x0960024833a02a06 0x00960024833a02a0 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z1139 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xeff81fff3fe03e0f 0xfeff81fff3fe03e0

def z1140 : W := mkw 0x6020224837ebbe0e 0x06020224837ebbe0 0x600000003fe1fe08 0x0600000003fe1fe0

def z1141 : W := mkw 0x8fdfddb7c0494140 0x88fdfddb7c049414 0xdfffffffc3f9c1cf 0xfdfffffffc3f9c1c

def z1142 : W := mkw 0x0941453440000000 0x0094145344000000 0x81e3e7f800000001 0x081e3e7f80000000

def z1143 : W := mkw 0x8fdfddb7c8140000 0x08fdfddb7c814000 0x9fffffffc01e0007 0xf9fffffffc01e000

def z1144 : W := mkw 0x4dde800018dd0000 0x04dde800018dd000 0x5fffe0001ff9c00b 0xe5fffe0001ff9c00

def z1145 : W := mkw 0x0021641c6202c312 0x40021641c6202c31 0xb067ee3ce007c737 0xab067ee3ce007c73

def z1146 : W := mkw 0x8fdfddb7c0490000 0x08fdfddb7c049000 0x8fffffffc3e1c007 0xf8fffffffc3e1c00

def z1147 : W := mkw 0x8f55ddb7c0000000 0x08f55ddb7c000000 0x8fe4ffffc0000005 0xf8fe4ffffc000000

def z1148 : W := mkw 0xcfdfddb7d0c90000 0x0cfdfddb7d0c9000 0x8fffffffc0e00007 0xf8fffffffc0e0000

def z1149 : W := mkw 0x96155db7cc1414a9 0x096155db7cc1414a 0xfe7ffffffc1e3fff 0xffe7ffffffc1e3ff

def z1150 : W := mkw 0x0021665c6322eb56 0xc0021665c6322eb5 0xb067ee3ce307ffff 0xab067ee3ce307fff

def z1151 : W := mkw 0x0021661c7382e316 0x40021661c7382e31 0xf067ee3cffe7e73f 0xaf067ee3cffe7e73

def z1152 : W := mkw 0x008b06cd01696b46 0x8008b06cd01696b4 0xd19b1fff03f9ffcf 0x7d19b1fff03f9ffc

def z1153 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fffffffc00039c7 0xf8fffffffc00039c

def z1154 : W := mkw 0x8bcbddb540000000 0x08bcbddb54000000 0x8ffbffff00000007 0xf8ffbffff0000000

def z1155 : W := mkw 0x008b04c500694940 0x8008b04c50069494 0x519b11c703f9d9cb 0x7519b11c703f9d9c

def z1156 : W := mkw 0x008b46d541696944 0x8008b46d54169694 0xd19ff7c7c3f9f9cf 0x7d19ff7c7c3f9f9c

def z1157 : W := mkw 0x0021641c6202c312 0x40021641c6202c31 0x3067e83ce007e73e 0xa3067e83ce007e73

def z1158 : W := mkw 0x002062186302a216 0x4002062186302a21 0xb067ee38e307e63f 0xab067ee38e307e63

def z1159 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe01ff81fe03e05 0x5cfe01ff81fe03e0

def z1160 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xffe41fffffe63fff 0xfffe41fffffe63ff

def z1161 : W := mkw 0x8fdfddb7c4001408 0x08fdfddb7c400140 0xaffffffffc000607 0xfaffffffffc00060

def z1162 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xa067ee38e307e63d 0xaa067ee38e307e63

def z1163 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8fe7effcc0000007 0xa8fe7effcc000000

def z1164 : W := mkw 0x0b601b2833802206 0x00b601b283380220 0xefe01ff83fe0260d 0xfefe01ff83fe0260

def z1165 : W := mkw 0x9f54d932cc1414a9 0x09f54d932cc1414a 0xfffcfffffc1e3fff 0xffffcfffffc1e3ff

def z1166 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e7eff8c0000001 0x881e7eff8c000000

def z1167 : W := mkw 0x4d74a0003a968000 0x04d74a0003a96800 0x7fe7e0003fe7c00b 0xe7fe7e0003fe7c00

def z1168 : W := mkw 0x2b401b6815a03e0e 0x02b401b6815a03e0 0xef801ff83ce03e0c 0xfef801ff83ce03e0

def z1169 : W := mkw 0x8fdfddb7c4001408 0x08fdfddb7c400140 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z1170 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xd19f17c7c3fff9ff 0x7d19f17c7c3fff9f

def z1171 : W := mkw 0x2020224837ebff5e 0xc2020224837ebff5 0x700000003ffffff8 0x0700000003ffffff

def z1172 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c1007fc1e3ffa 0x57e1c1007fc1e3ff

def z1173 : W := mkw 0xcdfea083badf8000 0x0cdfea083badf800 0x7fffe0033fffc00b 0xe7fffe0033fffc00

def z1174 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81e3eff800000005 0xa81e3eff80000000

def z1175 : W := mkw 0x008b46d541696944 0x8008b46d54169694 0xd19b1fffc3f9f9cf 0x7d19b1fffc3f9f9c

def z1176 : W := mkw 0x0021665c6322eb16 0x40021665c6322eb1 0xb1e7effce3e7e73f 0xab1e7effce3e7e73

def z1177 : W := mkw 0x0021669d6302e356 0xc0021669d6302e35 0xb067ee3fe307e7ff 0xab067ee3fe307e7f

def z1178 : W := mkw 0x0021665c6322eb16 0x40021665c6322eb1 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z1179 : W := mkw 0x0001064401206904 0x0000106440120690 0xd19b17c703f9f9cf 0x7d19b17c703f9f9c

def z1180 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0xafffffffe0060637 0xfafffffffe006063

def z1181 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x3e1c1807fc1e3ff6 0x93e1c1807fc1e3ff

def z1182 : W := mkw 0x89cbc5b540494140 0x889cbc5b54049414 0x81e3e7f80001c001 0x081e3e7f80001c00

def z1183 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe41ff83fe63e0f 0xfffe41ff83fe63e0

def z1184 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xf067ee3ce31fffff 0xaf067ee3ce31ffff

def z1185 : W := mkw 0x89cbc5b540000000 0x089cbc5b54000000 0x81fbe7ff00000003 0x081fbe7ff0000000

def z1186 : W := mkw 0x4ddea00018df8000 0x04ddea00018df800 0x5f9fe0001fffc00b 0x65f9fe0001fffc00

def z1187 : W := mkw 0x141400028c1414a9 0x0141400028c1414a 0x7e1c0007fc1e3ffa 0xe7e1c0007fc1e3ff

def z1188 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffbe0003fffc009 0x47ffbe0003fffc00

def z1189 : W := mkw 0x8bcbddb540000000 0x08bcbddb54000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z1190 : W := mkw 0x0021641c6202c312 0x40021641c6202c31 0x3067e83ce307c73b 0xa3067e83ce307c73

def z1191 : W := mkw 0x800145b540000000 0x0800145b54000000 0x8067effcc0000007 0xa8067effcc000000

def z1192 : W := mkw 0x8fdfddb7c8140000 0x08fdfddb7c814000 0xaffffffffc060007 0xfaffffffffc06000

def z1193 : W := mkw 0x8fdfddb7c0000000 0x08fdfddb7c000000 0x8ffcffffc0000004 0xd8ffcffffc000000

def z1194 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe807ffffe7ff 0xe7fffe807ffffe7f

def z1195 : W := mkw 0x0b415d3444001408 0x00b415d344400140 0xffe7fffcfc063f3f 0xfffe7fffcfc063f3

def z1196 : W := mkw 0x0021661c6302e316 0x40021661c6302e31 0xb067fe3fe307ffff 0xbb067fe3fe307fff

def z1197 : W := mkw 0x2b401b6015a03c0c 0x02b401b6015a03c0 0xcfe01ff81fe0380d 0xfcfe01ff81fe0380

def z1198 : W := mkw 0x89cbc5b540490000 0x089cbc5b54049000 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z1199 : W := mkw 0xc9cbc5b550c90000 0x0c9cbc5b550c9000 0x81e3e7f800e00001 0x081e3e7f800e0000

def z1200 : W := mkw 0x8fdfddb7c8140000 0x08fdfddb7c814000 0xcfffffffdc180007 0xfcfffffffdc18000

def z1201 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x2fffe0003fe7c003 0xe2fffe0003fe7c00

def z1202 : W := mkw 0x2b601b6833a02a06 0x02b601b6833a02a0 0xefe01ff83fe0000d 0xfefe01ff83fe0000

def z1203 : W := mkw 0x0ddfc49540000000 0x00ddfc4954000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1204 : W := mkw 0x008b06c501696944 0x8008b06c50169694 0xf19b17c723ffffff 0x7f19b17c723fffff

def z1205 : W := mkw 0xc49fe497c85fc110 0x4c49fe497c85fc11 0x101fe007c01fc132 0x0101fe007c01fc13

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z7,z5,z6]),(0,[z0,z1,z8,z3,z9,z5,z6]),(0,[z0,z1,z10,z3,z4,z5,z6]),(0,[z11,z12,z1,z3,z4,z5,z6])],[(1,[z13,z0,z14,z4,z5,z6]),(0,[z0,z15,z3,z16,z4,z5,z6]),(0,[z0,z15,z1,z3,z4,z5,z17]),(0,[z0,z1,z18,z3,z4,z5,z6]),(0,[z0,z1,z19,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z20,z6]),(0,[z0,z21,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z22,z6]),(0,[z0,z1,z23,z3,z4,z5,z24]),(0,[z0,z1,z25,z3,z4,z5,z6]),(0,[z26,z0,z1,z3,z4,z5,z6])],[(0,[z27,z1,z28,z3,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z30,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z31])],[(0,[z32,z0,z1,z3,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z34,z6]),(0,[z35,z0,z1,z3,z4,z5,z6]),(0,[z36,z0,z37,z3,z4,z5,z6])],[(1,[z38,z1,z39,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z40]),(0,[z41,z0,z42,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z43,z6]),(0,[z0,z1,z3,z4,z5,z44,z45]),(0,[z0,z1,z46,z47,z4,z5,z6]),(0,[z0,z1,z48,z3,z4,z5,z29])],[(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z50,z5,z6]),(0,[z0,z1,z3,z4,z51,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z52]),(0,[z0,z1,z53,z3,z4,z5,z6]),(0,[z0,z1,z3,z54,z4,z5,z6]),(1,[z11,z0,z3,z4,z55,z6]),(0,[z0,z1,z56,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z57]),(0,[z0,z1,z3,z4,z5,z6,z58]),(0,[z0,z1,z3,z4,z5,z17,z59]),(0,[z0,z1,z3,z4,z60,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z5,z61]),(0,[z0,z1,z62,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z59])],[(0,[z0,z1,z3,z4,z63,z5,z6]),(0,[z64,z0,z1,z3,z4,z5,z6]),(0,[z65,z0,z1,z39,z4,z5,z6]),(0,[z66,z0,z1,z3,z67,z4,z5]),(0,[z0,z1,z3,z4,z5,z68,z17])],[(0,[z69,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z70]),(0,[z0,z1,z71,z3,z4,z5,z6]),(0,[z0,z1,z23,z3,z4,z5,z6])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(1,[z0,z1,z3,z72,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z17]),(0,[z73,z0,z1,z8,z3,z4,z5]),(0,[z66,z0,z37,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z74])],[(0,[z75,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z76,z3,z4,z5,z6])],[(0,[z77,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z78,z6]),(0,[z0,z1,z47,z3,z4,z79,z6]),(0,[z80,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z81])],[(0,[z0,z1,z3,z4,z82,z5,z6])],[(0,[z83,z84,z1,z3,z4,z5,z6]),(0,[z0,z1,z85,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z86,z6,z45])]],
   [[(0,[z0,z1,z3,z4,z87,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z70]),(0,[z0,z1,z88,z3,z4,z5,z6])],[(0,[z0,z27,z89,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z91,z6]),(1,[z75,z1,z3,z4,z34,z6]),(0,[z92,z0,z1,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z93,z4,z5,z6]),(0,[z94,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z95,z5,z6])],[(1,[z96,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z97,z6]),(0,[z0,z1,z3,z4,z5,z17,z58])],[(0,[z98,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z33,z5,z6]),(1,[z0,z99,z3,z4,z5,z6]),(0,[z73,z0,z100,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z101,z29]),(0,[z0,z1,z3,z4,z5,z6,z102]),(0,[z0,z1,z103,z3,z4,z5,z6])],[(1,[z69,z28,z3,z4,z5,z6]),(0,[z0,z1,z104,z3,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z5,z6]),(0,[z106,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z47,z3,z4,z5,z6]),(0,[z0,z1,z23,z3,z4,z107,z6]),(0,[z0,z1,z3,z4,z5,z29,z108]),(0,[z0,z1,z3,z4,z5,z109,z17])],[(1,[z0,z1,z3,z4,z5,z110]),(0,[z0,z1,z111,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z70,z29]),(0,[z0,z112,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z113,z5,z6]),(0,[z65,z0,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z114,z6]),(0,[z75,z0,z1,z3,z4,z115,z6]),(0,[z0,z1,z116,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z29]),(0,[z117,z0,z1,z3,z4,z5,z6])],[(0,[z13,z0,z1,z14,z4,z5,z6]),(0,[z0,z1,z118,z3,z4,z5,z6]),(0,[z0,z1,z119,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z4,z5,z6])]],
   [[(0,[z0,z1,z121,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z122,z6]),(0,[z0,z89,z1,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z123])],[(0,[z124,z0,z1,z3,z4,z5,z6]),(0,[z36,z0,z27,z3,z4,z5,z6]),(1,[z0,z1,z3,z125,z5,z6]),(0,[z0,z1,z3,z4,z126,z5,z6]),(0,[z0,z1,z3,z4,z127,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z128]),(0,[z0,z129,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z130,z5,z6]),(0,[z0,z1,z3,z4,z5,z131,z6])],[(0,[z38,z0,z104,z3,z4,z5,z6]),(0,[z73,z66,z1,z3,z4,z5,z6]),(1,[z0,z89,z132,z4,z5,z6]),(0,[z0,z1,z3,z4,z133,z5,z6]),(0,[z0,z1,z3,z4,z5,z134,z6]),(1,[z0,z1,z3,z4,z5,z135]),(0,[z136,z0,z1,z3,z4,z5,z6]),(0,[z137,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z138,z6]),(0,[z0,z139,z1,z3,z4,z5,z6])],[(1,[z0,z1,z47,z140,z5,z6]),(1,[z0,z1,z141,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z17,z142])],[(0,[z0,z1,z3,z4,z5,z143,z6]),(0,[z0,z144,z1,z3,z4,z5,z6]),(0,[z0,z15,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z6,z145])],[(0,[z146,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z147,z5,z6]),(0,[z0,z1,z47,z3,z148,z5,z6]),(0,[z0,z1,z3,z149,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z86,z17]),(0,[z0,z1,z3,z4,z5,z6,z150]),(0,[z0,z1,z48,z3,z4,z5,z86])],[(0,[z13,z0,z1,z3,z4,z5,z17]),(0,[z0,z151,z1,z3,z4,z55,z6]),(0,[z0,z1,z47,z3,z140,z5,z6]),(0,[z0,z1,z152,z3,z4,z5,z6])],[(0,[z0,z1,z153,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z154,z5,z6]),(0,[z0,z1,z3,z155,z4,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z59])]],
   [[(0,[z1,z3,z4,z115,z5,z34,z6]),(0,[z0,z1,z156,z3,z4,z5,z6]),(0,[z157,z0,z1,z3,z4,z5,z17]),(0,[z158,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z6])],[(0,[z36,z0,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z159,z5,z6]),(0,[z38,z0,z1,z39,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z160,z6]),(0,[z0,z37,z3,z4,z5,z6,z101]),(0,[z0,z1,z3,z4,z5,z6,z161]),(0,[z0,z1,z3,z120,z4,z107,z6]),(0,[z0,z1,z3,z120,z4,z60,z6]),(0,[z0,z1,z3,z4,z162,z5,z45])],[(0,[z0,z1,z3,z163,z4,z5,z6]),(0,[z0,z1,z4,z5,z17,z6,z29])],[(0,[z164,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z165,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z166,z6]),(0,[z0,z1,z3,z4,z167,z5,z6]),(0,[z168,z0,z1,z3,z4,z5,z6])],[(0,[z69,z0,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z169,z6]),(0,[z0,z1,z3,z170,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z68,z29]),(0,[z0,z1,z3,z4,z5,z171,z6]),(0,[z0,z1,z3,z4,z5,z6,z172])],[(0,[z0,z1,z3,z4,z5,z173,z6]),(0,[z0,z1,z3,z4,z55,z5,z17]),(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z0,z175,z1,z3,z4,z5,z6])],[(0,[z176,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z177,z3,z4,z5,z6]),(0,[z0,z1,z178,z3,z4,z5,z6]),(0,[z0,z1,z3,z179,z4,z5,z29]),(0,[z0,z1,z3,z4,z60,z5,z17])]],
   [[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z180,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z181,z5,z6]),(0,[z0,z1,z3,z4,z182,z5,z6])],[(0,[z38,z0,z183,z3,z4,z5,z6]),(0,[z11,z96,z1,z3,z4,z5,z6])],[(0,[z0,z1,z184,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z17,z29]),(0,[z185,z0,z1,z3,z4,z5,z6])],[(0,[z1,z186,z3,z39,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z187]),(0,[z0,z1,z3,z4,z5,z188,z6]),(0,[z0,z1,z189,z3,z4,z5,z6]),(0,[z0,z89,z132,z3,z4,z5,z6]),(0,[z0,z1,z190,z3,z4,z5,z6]),(1,[z84,z1,z3,z4,z5,z6]),(0,[z191,z0,z1,z3,z4,z5,z6]),(0,[z12,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z6,z45]),(0,[z0,z192,z1,z3,z4,z5,z6])],[(1,[z176,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z193,z6]),(0,[z0,z1,z3,z4,z115,z68,z6]),(0,[z0,z1,z3,z4,z5,z194,z6])],[(0,[z0,z1,z3,z4,z5,z195,z6]),(0,[z11,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z196,z3,z4,z5,z6])],[(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z197,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z198,z5,z6])],[(1,[z0,z1,z3,z4,z5,z195]),(0,[z0,z1,z3,z4,z199,z5,z6]),(0,[z0,z1,z200,z3,z4,z68,z6])]],
   [[(0,[z201,z0,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z0,z1,z203,z3,z4,z5,z6])],[(0,[z0,z1,z3,z204,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z205]),(0,[z66,z1,z3,z4,z5,z70,z6]),(1,[z0,z1,z3,z4,z5,z206]),(0,[z0,z1,z3,z4,z5,z207,z17]),(0,[z0,z1,z3,z4,z5,z44,z6])],[(0,[z0,z1,z3,z4,z208,z5,z6]),(1,[z0,z1,z3,z4,z5,z209]),(0,[z0,z1,z3,z210,z4,z5,z6])],[(0,[z211,z0,z1,z3,z4,z5,z6]),(0,[z0,z212,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z5,z6]),(1,[z0,z1,z3,z4,z5,z213]),(0,[z0,z1,z214,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z215,z5,z6]),(0,[z216,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z217,z6])],[(0,[z0,z1,z3,z218,z4,z5,z6]),(0,[z0,z1,z3,z219,z4,z5,z6]),(0,[z32,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z220,z4,z5,z6]),(0,[z0,z1,z47,z3,z4,z5,z17]),(0,[z0,z1,z221,z3,z4,z68,z6])],[(0,[z0,z1,z3,z222,z4,z5,z6]),(0,[z0,z1,z3,z33,z5,z223,z6]),(0,[z0,z1,z3,z224,z4,z5,z6]),(1,[z66,z1,z3,z4,z5,z70]),(0,[z0,z1,z3,z4,z225,z5,z6]),(0,[z0,z37,z1,z3,z4,z5,z44]),(0,[z0,z112,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z226,z4,z5,z6]),(1,[z0,z1,z227,z3,z5,z6])],[(0,[z0,z28,z3,z4,z55,z5,z6]),(0,[z65,z0,z1,z3,z4,z5,z17]),(0,[z0,z42,z1,z3,z4,z5,z6]),(0,[z0,z1,z228,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z229,z6]),(0,[z13,z0,z1,z132,z4,z5,z6]),(0,[z0,z1,z132,z3,z4,z5,z230]),(0,[z0,z1,z3,z231,z4,z5,z6])]],
   [[(0,[z232,z1,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z86,z29]),(0,[z0,z1,z3,z4,z5,z233,z6])],[(1,[z0,z1,z3,z4,z5,z234]),(0,[z13,z0,z1,z3,z4,z5,z29])],[(0,[z0,z1,z235,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z230]),(0,[z0,z1,z3,z236,z4,z5,z6]),(0,[z0,z151,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z237,z4,z5,z6])],[(0,[z0,z1,z238,z3,z4,z5,z6]),(0,[z0,z1,z3,z239,z4,z5,z6]),(0,[z0,z1,z3,z4,z240,z5,z6])],[(0,[z73,z0,z1,z3,z4,z5,z45]),(0,[z66,z0,z1,z8,z3,z4,z5]),(0,[z13,z0,z1,z3,z4,z199,z6]),(0,[z0,z1,z3,z241,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z162,z5])],[(0,[z13,z0,z3,z14,z4,z5,z6])],[(0,[z0,z27,z3,z4,z5,z6,z101]),(0,[z0,z151,z1,z3,z4,z5,z135]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z0,z243,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z4,z223,z6])],[(0,[z0,z1,z3,z244,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z34,z29]),(0,[z0,z1,z245,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z246,z5,z6]),(0,[z0,z1,z3,z4,z5,z247,z6]),(0,[z35,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z6,z59])]],
   [[(0,[z0,z1,z3,z248,z4,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z249,z3,z4,z33,z5]),(0,[z0,z1,z3,z4,z55,z5,z29]),(0,[z0,z1,z8,z3,z4,z5,z17])],[(0,[z0,z1,z3,z39,z4,z5,z6]),(0,[z0,z1,z250,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z251,z5,z6]),(0,[z0,z1,z3,z4,z252,z5,z6]),(0,[z66,z0,z1,z3,z4,z5,z70]),(0,[z0,z1,z3,z4,z253,z5,z6]),(0,[z254,z0,z1,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z44]),(0,[z0,z1,z3,z4,z5,z255,z6]),(0,[z256,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z257,z6,z59])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z258,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z259,z6]),(0,[z0,z1,z3,z4,z60,z5,z29])],[(0,[z0,z260,z1,z3,z4,z5,z6]),(0,[z0,z1,z261,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z262,z6]),(0,[z0,z1,z140,z4,z148,z5,z6]),(0,[z157,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z263,z3,z4,z5,z6]),(0,[z0,z1,z3,z14,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z86,z101])],[(0,[z0,z1,z3,z4,z5,z6,z264]),(0,[z0,z1,z265,z3,z4,z5,z6]),(0,[z0,z1,z23,z3,z4,z5,z29])],[(0,[z266,z0,z1,z3,z4,z5,z6]),(0,[z232,z1,z3,z39,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z267,z6]),(0,[z0,z1,z3,z4,z5,z268,z29]),(0,[z0,z1,z3,z4,z5,z6,z269]),(0,[z0,z1,z3,z3,z4,z5,z29])],[(0,[z232,z0,z1,z3,z4,z5,z6]),(0,[z75,z0,z1,z3,z4,z34,z6]),(0,[z270,z0,z1,z3,z4,z5,z6]),(0,[z13,z0,z89,z3,z4,z5,z6]),(1,[z0,z151,z3,z4,z207,z6])]],
   [[(0,[z0,z1,z3,z271,z4,z5,z6]),(0,[z0,z1,z3,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z181,z5,z17]),(0,[z0,z1,z3,z4,z55,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z272])],[(0,[z0,z1,z273,z3,z4,z5,z6]),(0,[z0,z1,z274,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z148,z5,z6]),(0,[z0,z1,z275,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z33,z5,z6]),(0,[z0,z1,z276,z3,z4,z5,z6]),(0,[z277,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z278,z3,z4,z5,z29])],[(0,[z0,z1,z279,z3,z4,z5,z6])],[(0,[z280,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z74])],[(0,[z0,z1,z3,z4,z5,z6,z281]),(0,[z0,z1,z3,z282,z4,z5,z6]),(0,[z0,z1,z283,z3,z4,z5,z6]),(0,[z0,z1,z200,z3,z120,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z284]),(0,[z0,z1,z3,z4,z162,z5,z6])],[(0,[z0,z285,z1,z3,z4,z5,z6]),(1,[z0,z286,z3,z4,z5,z6]),(0,[z0,z1,z287,z3,z4,z5,z6]),(0,[z0,z1,z46,z3,z4,z5,z128])],[(0,[z0,z1,z3,z4,z288,z5,z6]),(0,[z0,z1,z47,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z6,z289])]],
   [[(0,[z0,z1,z3,z290,z4,z5,z6]),(0,[z0,z1,z291,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z17])],[(0,[z65,z0,z1,z3,z4,z5,z29]),(0,[z292,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z16,z148,z5,z6]),(0,[z0,z1,z293,z3,z4,z5,z6]),(0,[z117,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z29,z294])],[(0,[z0,z1,z3,z4,z295,z5,z6]),(0,[z0,z1,z3,z4,z5,z296,z6]),(0,[z0,z1,z297,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z107,z34,z6]),(0,[z0,z1,z298,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z4,z5,z29]),(0,[z0,z1,z278,z3,z4,z5,z6]),(0,[z0,z299,z1,z3,z4,z5,z6]),(0,[z300,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z33,z5,z17]),(0,[z0,z1,z3,z301,z4,z5,z6]),(0,[z302,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z142]),(0,[z0,z1,z303,z3,z4,z5,z6])],[(0,[z32,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z132,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z207,z6]),(1,[z0,z1,z3,z4,z5,z102]),(0,[z0,z1,z3,z4,z5,z304,z6]),(0,[z0,z1,z3,z4,z305,z5,z6])],[(0,[z0,z28,z3,z14,z4,z5,z6]),(0,[z0,z151,z1,z3,z4,z5,z206])],[(0,[z0,z1,z306,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z307,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z213]),(1,[z0,z1,z23,z4,z68,z6]),(0,[z0,z1,z3,z4,z5,z6,z308])],[(0,[z0,z1,z3,z4,z5,z6,z6]),(1,[z0,z1,z221,z4,z107,z6]),(0,[z0,z1,z141,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z309,z29])]],
   [[(0,[z1,z28,z3,z39,z4,z5,z6]),(0,[z0,z1,z3,z310,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z311]),(0,[z0,z1,z3,z4,z312,z5,z6])],[(0,[z0,z1,z313,z3,z4,z5,z6])],[(0,[z69,z232,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z314,z4,z5,z6]),(0,[z0,z1,z315,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z128]),(0,[z316,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z317,z6]),(0,[z0,z1,z8,z3,z4,z5,z29])],[(1,[z0,z1,z3,z318,z5,z6]),(0,[z0,z1,z3,z4,z319,z5,z6])],[(0,[z0,z1,z3,z4,z320,z5,z6]),(0,[z0,z1,z3,z4,z321,z5,z6]),(0,[z0,z1,z186,z3,z4,z5,z6]),(0,[z0,z1,z3,z9,z148,z5,z6]),(0,[z0,z1,z3,z4,z5,z322,z6]),(0,[z0,z1,z3,z4,z5,z323,z6]),(0,[z0,z1,z275,z4,z5,z17,z6]),(0,[z0,z1,z3,z324,z4,z5,z6])],[(0,[z38,z0,z1,z3,z72,z5,z6]),(0,[z0,z1,z3,z4,z325,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z326]),(1,[z0,z1,z3,z120,z60,z6]),(0,[z0,z1,z3,z5,z6,z289,z45])],[(0,[z69,z0,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z327,z6]),(0,[z328,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z329,z6]),(0,[z0,z1,z330,z3,z4,z5,z6]),(0,[z0,z1,z3,z331,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z332])]],
   [[(0,[z0,z1,z99,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z333,z5,z6]),(0,[z0,z1,z3,z4,z334,z5,z6]),(0,[z0,z1,z221,z3,z4,z5,z161])],[(0,[z0,z151,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z39,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z335,z6])],[(0,[z0,z1,z3,z4,z5,z336,z6]),(0,[z0,z1,z3,z337,z4,z5,z6]),(0,[z338,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z161]),(0,[z0,z1,z3,z4,z5,z17,z6])],[(0,[z0,z1,z339,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z181,z5,z29]),(0,[z0,z1,z340,z3,z4,z5,z6]),(0,[z0,z1,z8,z48,z3,z4,z5])],[(0,[z75,z1,z28,z3,z4,z5,z6]),(0,[z341,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z342]),(0,[z343,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z344,z5,z6]),(0,[z345,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z346,z6]),(0,[z0,z1,z3,z4,z5,z6,z347]),(1,[z0,z1,z3,z4,z122,z6]),(0,[z0,z1,z3,z4,z348,z5,z6]),(0,[z0,z1,z23,z3,z4,z68,z6])],[(0,[z65,z1,z28,z3,z4,z5,z6]),(0,[z38,z65,z1,z3,z4,z5,z6]),(0,[z32,z1,z3,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z349,z5,z6]),(0,[z0,z1,z3,z60,z5,z257,z6])],[(0,[z232,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z350,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z351,z6]),(0,[z0,z1,z3,z14,z4,z5,z6]),(0,[z0,z352,z1,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z101]),(1,[z0,z1,z3,z4,z138,z6]),(0,[z0,z1,z221,z4,z107,z5,z6])]],
   [[(0,[z0,z1,z353,z3,z4,z5,z6]),(0,[z41,z0,z99,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z16,z4,z5,z17]),(0,[z0,z1,z354,z3,z4,z5,z6])],[(0,[z0,z89,z28,z3,z4,z5,z6]),(0,[z0,z151,z28,z3,z4,z5,z6]),(0,[z355,z0,z1,z3,z4,z5,z6]),(0,[z356,z0,z1,z3,z4,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z101,z45]),(0,[z0,z1,z3,z4,z148,z5,z17]),(0,[z197,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z275,z3,z4,z5,z17])],[(0,[z0,z357,z1,z3,z4,z5,z6]),(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z359,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z360])],[(0,[z41,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z361,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z24,z6])],[(0,[z0,z1,z339,z28,z3,z4,z5]),(0,[z38,z0,z1,z3,z125,z5,z6]),(0,[z66,z0,z1,z3,z307,z5,z6]),(0,[z0,z1,z362,z3,z4,z5,z6]),(0,[z363,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z364]),(0,[z0,z1,z3,z4,z5,z44,z29]),(0,[z0,z1,z3,z67,z4,z5,z44]),(0,[z0,z1,z3,z365,z4,z5,z6]),(0,[z0,z1,z3,z4,z366,z5,z6]),(0,[z367,z0,z1,z3,z4,z5,z6])],[(0,[z368,z0,z1,z3,z4,z5,z6]),(0,[z66,z0,z1,z3,z4,z5,z45]),(0,[z0,z1,z369,z3,z4,z5,z6]),(0,[z0,z1,z370,z3,z4,z5,z6]),(0,[z0,z371,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z162,z5,z17])],[(0,[z0,z1,z3,z4,z33,z5,z29]),(0,[z372,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z373,z3,z4,z5,z6])],[(0,[z0,z1,z3,z374,z4,z33,z5]),(0,[z0,z1,z3,z375,z4,z5,z6]),(0,[z0,z1,z3,z376,z4,z5,z6]),(1,[z0,z15,z3,z16,z5,z6]),(0,[z377,z0,z1,z3,z4,z5,z6]),(1,[z0,z37,z3,z4,z5,z101]),(0,[z0,z1,z3,z4,z378,z5,z6])]],
   [[(1,[z379,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z380,z5,z6]),(0,[z381,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z382,z5,z6]),(0,[z0,z1,z3,z4,z383,z5,z6]),(0,[z0,z1,z3,z4,z384,z5,z6]),(0,[z0,z1,z48,z3,z4,z162,z6])],[(0,[z385,z0,z1,z3,z4,z5,z6]),(0,[z75,z232,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z127,z5,z6]),(1,[z0,z1,z3,z4,z5,z262]),(0,[z0,z1,z3,z4,z5,z257,z6])],[(0,[z176,z0,z1,z28,z3,z4,z5]),(0,[z386,z0,z1,z3,z4,z5,z6]),(0,[z387,z0,z1,z3,z4,z5,z6]),(1,[z144,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z55,z5,z207,z6]),(0,[z0,z1,z3,z4,z79,z5,z6]),(0,[z0,z1,z3,z120,z4,z68,z6]),(0,[z0,z1,z3,z4,z5,z388,z6]),(0,[z0,z1,z389,z3,z4,z5,z6])],[(0,[z0,z1,z390,z3,z4,z5,z6]),(0,[z0,z1,z3,z391,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z392,z6])],[(0,[z32,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z9,z4,z5,z17]),(0,[z0,z1,z132,z3,z4,z5,z17]),(0,[z0,z1,z3,z181,z148,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z393])],[(0,[z41,z0,z1,z3,z4,z115,z6]),(0,[z0,z1,z394,z3,z4,z5,z6])],[(0,[z395,z0,z1,z3,z4,z5,z6]),(0,[z396,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z397,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z398]),(0,[z399,z0,z1,z3,z4,z5,z6])],[(0,[z400,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z141,z3,z4,z5,z17])]],
   [[(0,[z0,z401,z1,z3,z4,z5,z6]),(0,[z0,z402,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z403,z5,z6]),(0,[z0,z1,z3,z4,z5,z404,z6]),(0,[z0,z1,z3,z4,z5,z405,z6]),(0,[z0,z1,z221,z3,z155,z5,z6])],[(0,[z0,z1,z3,z406,z4,z5,z6]),(0,[z316,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z407,z5,z6])],[(0,[z408,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z114,z5,z6]),(0,[z0,z1,z3,z4,z409,z5,z6]),(0,[z0,z1,z23,z3,z4,z5,z74]),(1,[z0,z1,z3,z155,z5,z6])],[(0,[z0,z1,z3,z39,z4,z5,z29]),(0,[z41,z1,z3,z4,z115,z5,z6]),(0,[z0,z1,z410,z3,z4,z5,z6]),(0,[z411,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z23,z221,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z309])],[(0,[z0,z1,z186,z3,z4,z5,z17]),(0,[z36,z66,z0,z1,z3,z4,z5]),(0,[z0,z15,z1,z3,z16,z5,z6]),(0,[z36,z0,z3,z4,z5,z44,z6])],[(0,[z0,z1,z3,z4,z5,z412,z6]),(0,[z0,z1,z3,z4,z5,z6,z413])],[(0,[z232,z65,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z318,z5,z6]),(0,[z414,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z415,z4,z5,z6]),(0,[z0,z416,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z417,z1,z3,z4,z5,z6]),(0,[z418,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z419,z3,z4,z5,z6]),(0,[z0,z1,z3,z140,z60,z5,z6]),(0,[z420,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z421,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z422]),(0,[z423,z0,z1,z3,z4,z5,z6]),(0,[z0,z424,z1,z3,z4,z5,z6])],[(0,[z232,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z425,z3,z4,z5,z6]),(0,[z426,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z17])],[(0,[z0,z1,z249,z3,z4,z5,z6]),(0,[z0,z1,z3,z427,z4,z5,z6]),(0,[z0,z1,z3,z16,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z428,z6]),(0,[z0,z1,z3,z4,z5,z429,z6])],[(0,[z0,z1,z430,z3,z4,z5,z6]),(0,[z0,z132,z3,z14,z4,z5,z6]),(0,[z0,z1,z3,z4,z148,z5,z29]),(0,[z0,z1,z275,z3,z4,z5,z29])],[(0,[z0,z1,z3,z9,z5,z257,z6]),(0,[z75,z0,z1,z3,z120,z4,z6]),(0,[z0,z1,z3,z4,z431,z5,z6]),(0,[z0,z1,z3,z4,z5,z432,z6]),(0,[z0,z1,z433,z3,z4,z5,z6]),(0,[z0,z1,z434,z3,z4,z5,z6])],[(1,[z0,z100,z3,z4,z5,z6]),(0,[z0,z15,z1,z3,z181,z5,z6]),(0,[z0,z1,z3,z4,z5,z435,z6])],[(0,[z0,z1,z3,z4,z5,z29,z187]),(0,[z0,z1,z3,z4,z5,z29,z45]),(0,[z0,z1,z3,z4,z436,z5,z6]),(0,[z0,z1,z3,z67,z4,z5,z59]),(0,[z0,z1,z437,z3,z4,z5,z6])]],
   [[(0,[z32,z438,z1,z3,z4,z5,z6]),(0,[z36,z73,z0,z1,z3,z4,z5]),(0,[z73,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z439,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z4,z122,z6]),(0,[z0,z1,z3,z4,z5,z440,z6]),(0,[z0,z1,z3,z4,z162,z5,z29]),(0,[z0,z1,z354,z3,z4,z5,z17])],[(0,[z441,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z442,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z443]),(0,[z0,z1,z3,z67,z4,z5,z257])],[(0,[z0,z444,z1,z3,z4,z5,z6]),(0,[z0,z1,z445,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z20])],[(0,[z0,z1,z3,z4,z5,z342,z6]),(1,[z41,z1,z3,z4,z115,z6]),(0,[z0,z1,z46,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z366,z5,z17])],[(0,[z438,z0,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z446,z5,z6]),(0,[z0,z1,z3,z4,z5,z447,z6]),(0,[z0,z1,z448,z3,z4,z5,z6]),(0,[z0,z1,z3,z449,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z450,z17]),(0,[z0,z1,z3,z4,z5,z451,z6])],[(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z115,z5,z6]),(0,[z452,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z453,z5,z6]),(0,[z32,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z9,z4,z5,z29]),(0,[z0,z1,z132,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z207,z29])]],
   [[(0,[z0,z1,z3,z421,z4,z5,z6]),(0,[z0,z1,z454,z3,z4,z5,z6]),(0,[z0,z1,z3,z318,z4,z5,z6]),(0,[z455,z0,z1,z3,z4,z5,z6])],[(0,[z0,z456,z1,z3,z4,z5,z6]),(0,[z0,z1,z457,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z458,z6]),(0,[z0,z459,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z460,z6]),(0,[z0,z1,z3,z4,z461,z5,z6]),(0,[z0,z1,z3,z4,z5,z257,z17]),(0,[z0,z1,z200,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z162,z86])],[(0,[z462,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z463,z6]),(0,[z464,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z465,z5,z6]),(0,[z0,z1,z466,z3,z4,z5,z6]),(0,[z0,z1,z141,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z6,z29]),(0,[z0,z1,z3,z4,z5,z223,z17])],[(0,[z232,z1,z3,z4,z115,z5,z6]),(0,[z75,z1,z3,z4,z5,z34,z6]),(0,[z467,z0,z1,z3,z4,z5,z6]),(0,[z13,z379,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z391,z4,z5,z17])],[(0,[z0,z1,z468,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z17]),(0,[z469,z0,z1,z3,z4,z5,z6])],[(0,[z470,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z67,z4,z5]),(0,[z0,z1,z3,z4,z5,z471,z6]),(0,[z0,z1,z46,z3,z148,z5,z6]),(0,[z472,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z46,z3,z140,z5,z6])],[(0,[z0,z1,z3,z473,z4,z5,z6]),(0,[z0,z1,z186,z3,z4,z5,z110]),(0,[z0,z1,z3,z9,z4,z5,z6]),(1,[z0,z1,z178,z3,z4,z6])]],
   [[(0,[z474,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z186,z3,z4,z5,z29]),(0,[z475,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z140,z16,z5,z6]),(0,[z11,z0,z151,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z476,z6])],[(1,[z0,z1,z3,z4,z5,z311]),(0,[z0,z1,z3,z477,z4,z5,z6]),(0,[z0,z1,z3,z140,z9,z5,z6]),(0,[z66,z0,z1,z3,z4,z5,z6]),(1,[z260,z1,z3,z4,z5,z6]),(0,[z83,z144,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z478,z6]),(0,[z0,z1,z479,z3,z4,z5,z223]),(0,[z480,z0,z1,z3,z4,z5,z6])],[(1,[z65,z1,z186,z4,z5,z6]),(0,[z0,z1,z3,z4,z481,z5,z6]),(0,[z0,z1,z3,z4,z5,z482,z6]),(0,[z0,z3,z16,z4,z181,z5,z6]),(0,[z0,z1,z3,z483,z4,z5,z6]),(0,[z0,z1,z200,z3,z148,z5,z6]),(0,[z0,z1,z330,z3,z4,z5,z29])],[(0,[z0,z1,z3,z4,z5,z484,z6]),(0,[z0,z1,z200,z3,z140,z5,z6]),(0,[z0,z1,z3,z4,z5,z29,z59]),(0,[z0,z1,z200,z3,z4,z60,z6]),(0,[z0,z1,z3,z4,z485,z5,z6]),(0,[z0,z1,z3,z120,z60,z5,z6])],[(0,[z0,z1,z3,z4,z5,z486,z6]),(0,[z1,z3,z4,z5,z70,z6,z268]),(0,[z0,z1,z8,z3,z67,z5,z6])],[(0,[z65,z0,z1,z186,z4,z5,z6]),(0,[z487,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z29]),(0,[z0,z1,z3,z4,z5,z6,z488])],[(0,[z438,z1,z3,z4,z33,z5,z6]),(0,[z83,z0,z1,z3,z16,z5,z6]),(0,[z0,z1,z3,z489,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z101]),(0,[z0,z1,z490,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z491]),(0,[z0,z1,z3,z4,z492,z5,z6]),(0,[z0,z1,z48,z3,z4,z5,z45])],[(1,[z0,z1,z3,z4,z5,z326]),(0,[z0,z1,z3,z4,z5,z493,z6]),(0,[z0,z1,z494,z3,z4,z5,z6]),(0,[z0,z1,z495,z3,z4,z5,z6]),(0,[z0,z1,z496,z3,z4,z5,z6]),(0,[z0,z1,z497,z3,z4,z5,z6]),(0,[z0,z1,z3,z67,z4,z5,z6])]],
   [[(0,[z0,z1,z498,z3,z4,z5,z6]),(0,[z438,z0,z1,z3,z33,z5,z6]),(0,[z0,z1,z3,z499,z4,z5,z6]),(0,[z0,z1,z3,z4,z162,z5,z86])],[(0,[z0,z1,z3,z4,z500,z5,z6]),(0,[z0,z1,z3,z4,z5,z234,z6]),(0,[z0,z1,z3,z140,z181,z5,z6]),(0,[z501,z0,z1,z3,z4,z5,z6])],[(0,[z502,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z503,z4,z5,z6]),(0,[z0,z1,z3,z14,z4,z5,z29]),(0,[z0,z1,z3,z504,z4,z5,z6]),(0,[z0,z1,z3,z4,z107,z207,z6])],[(0,[z505,z0,z1,z3,z4,z5,z6]),(0,[z506,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z507,z5,z6]),(0,[z0,z1,z3,z125,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z55,z68,z6]),(1,[z0,z1,z3,z4,z5,z508]),(0,[z0,z1,z3,z4,z5,z509,z6]),(0,[z0,z1,z3,z510,z4,z5,z6])],[(0,[z32,z1,z28,z3,z4,z5,z6])],[(0,[z1,z28,z3,z4,z115,z5,z6]),(0,[z0,z1,z3,z4,z5,z511,z6]),(0,[z0,z27,z3,z4,z55,z5,z6]),(0,[z0,z1,z3,z4,z5,z512,z6]),(0,[z0,z15,z1,z3,z4,z5,z326])],[(0,[z0,z1,z513,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z34,z6]),(0,[z0,z1,z3,z4,z514,z5,z6])],[(0,[z515,z0,z1,z3,z4,z5,z6]),(0,[z83,z0,z1,z3,z181,z5,z6]),(0,[z0,z1,z3,z4,z516,z5,z6]),(1,[z0,z1,z3,z5,z6,z289])]],
   [[(1,[z0,z1,z3,z4,z317,z6]),(0,[z0,z1,z517,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z518,z5,z6]),(0,[z0,z1,z3,z4,z519,z5,z6]),(0,[z0,z1,z3,z520,z4,z5,z6]),(0,[z0,z1,z521,z3,z4,z5,z6]),(0,[z0,z1,z522,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z523]),(0,[z0,z524,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z525,z6]),(0,[z526,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z527,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z44,z6,z101]),(0,[z0,z1,z3,z4,z5,z17,z101]),(0,[z0,z1,z3,z4,z5,z528,z6]),(0,[z529,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z530,z3,z4,z5,z6]),(0,[z0,z1,z3,z60,z5,z223,z6]),(0,[z0,z1,z3,z4,z5,z531,z6]),(0,[z0,z1,z48,z3,z4,z6,z45])],[(0,[z532,z0,z1,z3,z4,z5,z6]),(1,[z83,z0,z3,z181,z5,z6]),(0,[z0,z1,z533,z3,z4,z5,z6]),(0,[z0,z37,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z534,z5,z6]),(0,[z0,z1,z3,z140,z33,z5,z6]),(0,[z0,z1,z535,z3,z4,z5,z6]),(0,[z0,z1,z3,z536,z4,z5,z6]),(0,[z0,z1,z3,z4,z207,z68,z6]),(0,[z0,z1,z46,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z257,z29])],[(0,[z0,z1,z3,z537,z4,z5,z6]),(0,[z0,z1,z4,z107,z5,z68,z6]),(0,[z0,z1,z3,z4,z5,z223,z29])],[(0,[z0,z1,z3,z4,z115,z5,z17]),(0,[z0,z1,z3,z4,z5,z6,z209]),(0,[z0,z1,z3,z4,z5,z6,z268]),(1,[z0,z1,z3,z307,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z20]),(0,[z0,z538,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z539,z6]),(0,[z0,z540,z1,z3,z4,z5,z6])],[(0,[z36,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z227,z3,z5,z6,z45])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z541]),(0,[z0,z1,z3,z4,z5,z450,z6]),(1,[z0,z42,z3,z4,z5,z6])],[(0,[z0,z1,z186,z3,z4,z5,z195]),(0,[z0,z1,z178,z3,z4,z33,z6]),(0,[z0,z1,z3,z4,z5,z6,z542]),(0,[z0,z1,z3,z4,z543,z5,z6]),(0,[z0,z1,z3,z4,z5,z458,z17]),(0,[z0,z1,z200,z3,z4,z5,z17])],[(0,[z0,z1,z28,z3,z4,z5,z17]),(0,[z0,z1,z3,z374,z4,z5,z6]),(0,[z0,z1,z3,z4,z544,z5,z6]),(0,[z545,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z546,z6]),(0,[z0,z1,z3,z4,z72,z5,z6]),(0,[z0,z1,z3,z4,z5,z547,z6]),(0,[z0,z1,z3,z548,z4,z5,z6]),(0,[z0,z1,z3,z549,z4,z5,z6]),(0,[z0,z1,z550,z3,z4,z5,z6])],[(0,[z0,z1,z3,z551,z4,z5,z6])],[(0,[z38,z0,z1,z186,z4,z5,z6]),(0,[z0,z1,z552,z3,z4,z5,z6]),(0,[z0,z1,z3,z553,z4,z5,z6]),(0,[z0,z1,z554,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z555,z5,z6]),(0,[z0,z1,z3,z4,z5,z223,z6]),(1,[z0,z1,z8,z3,z5,z59])],[(0,[z0,z1,z221,z3,z4,z5,z17])],[(0,[z38,z0,z1,z3,z4,z5,z342]),(0,[z0,z1,z3,z4,z5,z61,z6]),(0,[z83,z0,z15,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z556,z5,z6])]],
   [[(0,[z11,z0,z1,z3,z4,z207,z6]),(0,[z0,z1,z200,z3,z4,z223,z6])],[(0,[z0,z1,z3,z4,z5,z17,z268]),(0,[z66,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z140,z4,z5,z6]),(0,[z0,z1,z3,z4,z107,z5,z17])],[(0,[z69,z0,z1,z3,z4,z5,z6]),(0,[z0,z557,z1,z3,z4,z5,z6]),(0,[z0,z15,z1,z3,z4,z5,z262]),(1,[z0,z1,z46,z148,z5,z6]),(0,[z0,z558,z1,z3,z4,z5,z6]),(0,[z0,z559,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z560]),(0,[z0,z1,z3,z4,z561,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z562]),(0,[z0,z1,z563,z3,z4,z5,z17]),(0,[z564,z0,z1,z3,z4,z5,z6])],[(0,[z73,z0,z1,z3,z4,z5,z86]),(0,[z379,z0,z1,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z101]),(0,[z0,z1,z3,z4,z565,z5,z6]),(1,[z0,z1,z479,z3,z4,z5]),(0,[z0,z1,z566,z3,z4,z5,z6])],[(0,[z0,z96,z1,z3,z4,z5,z6]),(0,[z0,z424,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z6,z567]),(0,[z0,z1,z3,z4,z162,z86,z6])],[(0,[z0,z183,z1,z3,z4,z5,z6])],[(0,[z0,z1,z568,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z230]),(0,[z0,z1,z221,z3,z4,z5,z460]),(0,[z0,z1,z3,z4,z5,z569,z6])],[(0,[z570,z0,z1,z3,z4,z5,z6]),(1,[z438,z1,z3,z33,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z268]),(0,[z83,z0,z1,z3,z4,z5,z6]),(0,[z83,z0,z3,z4,z181,z5,z6]),(0,[z0,z1,z3,z4,z571,z5,z6]),(0,[z0,z1,z3,z4,z572,z5,z6]),(0,[z0,z1,z3,z67,z4,z5,z17]),(1,[z0,z1,z200,z3,z223,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z573]),(0,[z0,z1,z3,z4,z5,z574,z6]),(0,[z575,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z576]),(1,[z0,z1,z3,z4,z5,z460])],[(0,[z0,z1,z3,z4,z5,z577,z6]),(0,[z0,z1,z578,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z579,z6])],[(0,[z580,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z47,z140,z4,z5,z6]),(0,[z0,z1,z200,z3,z5,z257,z6]),(0,[z0,z1,z3,z581,z4,z5,z6])],[(1,[z0,z1,z339,z3,z4,z5]),(1,[z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z200,z3,z5,z223,z6])],[(0,[z0,z27,z3,z14,z4,z5,z6]),(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z132,z3,z4,z5,z61]),(0,[z0,z1,z227,z3,z4,z5,z6])],[(0,[z0,z1,z583,z3,z4,z5,z6]),(0,[z0,z151,z1,z3,z4,z207,z6])],[(0,[z0,z1,z584,z3,z4,z5,z6]),(1,[z36,z0,z3,z4,z5,z44]),(0,[z0,z1,z221,z3,z384,z5,z6]),(0,[z0,z1,z3,z4,z5,z562,z29]),(0,[z0,z1,z200,z8,z3,z5,z6]),(1,[z0,z1,z3,z4,z5,z217]),(0,[z0,z1,z585,z3,z4,z5,z6])],[(0,[z0,z586,z1,z3,z4,z5,z6]),(1,[z0,z104,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z33,z5,z6]),(0,[z0,z1,z46,z3,z4,z5,z29]),(0,[z515,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z8,z3,z4,z5,z257])]],
   [[(0,[z0,z27,z1,z3,z4,z5,z6]),(0,[z587,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z9,z4,z33,z5,z6]),(0,[z0,z1,z588,z3,z4,z5,z6]),(1,[z0,z1,z3,z384,z5,z6])],[(0,[z0,z1,z3,z4,z589,z5,z6]),(0,[z0,z1,z3,z33,z148,z5,z6]),(0,[z0,z1,z3,z590,z4,z5,z6]),(0,[z0,z1,z3,z9,z5,z223,z6]),(0,[z75,z0,z1,z200,z3,z4,z6]),(0,[z0,z1,z3,z4,z115,z5,z29]),(0,[z0,z1,z3,z4,z5,z591,z6]),(0,[z0,z1,z592,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z593,z6]),(0,[z0,z1,z3,z4,z5,z86,z44]),(0,[z0,z1,z46,z4,z148,z5,z6]),(0,[z0,z1,z48,z3,z4,z5,z6])],[(0,[z0,z37,z1,z3,z4,z5,z17]),(0,[z0,z594,z1,z3,z4,z5,z6])],[(0,[z0,z1,z595,z3,z4,z5,z6]),(0,[z0,z1,z200,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z6,z596]),(0,[z0,z1,z597,z3,z4,z5,z6])],[(0,[z0,z1,z28,z3,z4,z5,z29]),(0,[z232,z27,z1,z3,z4,z5,z6]),(0,[z438,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z598,z4,z5,z6]),(0,[z0,z1,z599,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z393,z29]),(0,[z0,z1,z3,z4,z600,z5,z6])],[(0,[z601,z0,z1,z3,z4,z5,z6]),(0,[z602,z0,z1,z3,z4,z5,z6]),(0,[z603,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z604,z3,z4,z5,z6])],[(0,[z0,z28,z3,z4,z5,z6,z101]),(0,[z11,z0,z3,z4,z55,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z217,z223])]],
   [[(0,[z0,z1,z47,z3,z4,z5,z102]),(0,[z0,z1,z3,z67,z5,z257,z6])],[(0,[z75,z0,z1,z3,z4,z5,z6]),(0,[z605,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z221,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z57,z29])],[(0,[z0,z1,z3,z4,z5,z606,z6]),(0,[z75,z0,z1,z3,z251,z5,z6]),(0,[z75,z0,z1,z3,z503,z5,z6]),(0,[z0,z607,z1,z3,z4,z5,z6]),(0,[z0,z1,z608,z3,z4,z5,z6])],[(0,[z0,z1,z100,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z609,z6]),(0,[z0,z1,z3,z4,z5,z610,z6]),(1,[z0,z1,z3,z4,z5,z24])],[(0,[z0,z1,z3,z4,z5,z6,z110]),(0,[z0,z1,z3,z4,z5,z6,z611]),(0,[z73,z1,z3,z4,z5,z6,z268]),(0,[z66,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z612,z3,z4,z5,z6]),(0,[z0,z1,z3,z613,z4,z5,z6]),(1,[z0,z1,z3,z4,z79,z6]),(0,[z0,z1,z3,z4,z107,z5,z29])],[(0,[z0,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z614]),(0,[z0,z615,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z616,z17]),(0,[z0,z1,z3,z4,z5,z617,z6])],[(0,[z618,z0,z1,z3,z4,z5,z6]),(1,[z0,z183,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z619,z5,z6]),(1,[z0,z1,z3,z170,z5,z6]),(1,[z0,z1,z3,z4,z199,z6]),(0,[z0,z1,z3,z620,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z233])],[(0,[z621,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z421,z4,z33,z6]),(0,[z66,z0,z1,z3,z170,z5,z6]),(0,[z13,z0,z1,z3,z127,z5,z6]),(0,[z0,z1,z622,z3,z4,z5,z6]),(0,[z0,z1,z3,z623,z4,z5,z6])]],
   [[(0,[z624,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z625,z3,z4,z5,z6]),(0,[z0,z1,z3,z626,z4,z5,z6]),(0,[z0,z1,z3,z627,z4,z5,z6])],[(0,[z0,z1,z3,z140,z4,z5,z17]),(0,[z0,z1,z221,z3,z4,z5,z6]),(0,[z0,z1,z628,z3,z4,z5,z6]),(0,[z629,z0,z1,z3,z4,z5,z6])],[(0,[z69,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z630,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z70,z6]),(0,[z73,z0,z37,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z631]),(0,[z0,z1,z632,z3,z4,z5,z6]),(0,[z0,z1,z3,z67,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z6,z633])],[(1,[z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z374,z4,z5]),(0,[z73,z0,z286,z3,z4,z5,z6]),(0,[z0,z1,z3,z634,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z635,z6])],[(0,[z636,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z251,z5,z6]),(1,[z0,z1,z3,z503,z5,z6]),(0,[z0,z89,z1,z3,z4,z5,z17]),(0,[z0,z151,z1,z3,z4,z5,z17]),(0,[z0,z1,z47,z3,z4,z5,z508]),(0,[z0,z1,z3,z4,z107,z5,z6])],[(1,[z232,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z637,z4,z5,z6]),(0,[z0,z1,z563,z3,z4,z5,z6]),(0,[z0,z1,z638,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z29,z422]),(0,[z0,z1,z3,z4,z5,z639,z6])],[(0,[z0,z1,z3,z4,z107,z115,z6]),(0,[z0,z1,z3,z4,z5,z6,z640]),(0,[z0,z1,z3,z4,z5,z508,z6]),(0,[z0,z1,z200,z3,z4,z107,z6]),(0,[z0,z1,z141,z4,z5,z6,z29])],[(0,[z0,z1,z3,z4,z5,z641,z6]),(0,[z0,z1,z642,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z643,z6]),(0,[z83,z0,z1,z3,z4,z5,z17]),(0,[z570,z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z644,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z645,z3,z4,z5,z6]),(0,[z646,z0,z1,z3,z4,z5,z6]),(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z0,z1,z648,z3,z4,z5,z6]),(0,[z649,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z650,z5,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z652,z6])],[(0,[z653,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z654,z5,z6]),(0,[z0,z1,z3,z4,z5,z34,z17]),(0,[z0,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z81,z6])],[(0,[z0,z1,z655,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z656,z6])],[(0,[z0,z1,z3,z4,z5,z6,z657]),(0,[z658,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z47,z3,z4,z138,z6]),(0,[z0,z1,z221,z3,z4,z107,z6])],[(0,[z0,z1,z659,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z120,z4,z6]),(0,[z0,z1,z46,z3,z4,z5,z635]),(0,[z0,z1,z141,z275,z4,z5,z6]),(0,[z0,z660,z1,z3,z4,z5,z6])],[(0,[z41,z0,z1,z200,z3,z4,z6]),(0,[z0,z1,z3,z4,z115,z5,z209]),(0,[z0,z1,z661,z3,z4,z5,z6])],[(0,[z0,z37,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z67,z4,z5,z101])],[(0,[z662,z0,z1,z3,z4,z5,z6]),(0,[z663,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z664,z6]),(0,[z0,z1,z23,z3,z4,z5,z17]),(0,[z0,z1,z8,z3,z60,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z665])]],
   [[(0,[z0,z27,z1,z3,z4,z5,z17]),(0,[z438,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z666,z3,z4,z5,z6]),(0,[z0,z151,z3,z4,z5,z207,z6]),(0,[z0,z1,z23,z4,z5,z68,z6])],[(1,[z12,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z667,z5,z6]),(0,[z0,z1,z3,z4,z5,z68,z6])],[(0,[z38,z1,z3,z39,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z668,z6]),(0,[z0,z1,z48,z3,z4,z5,z17])],[(1,[z0,z1,z249,z3,z4,z5])],[(0,[z232,z0,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z669,z6]),(0,[z38,z0,z1,z3,z4,z5,z311]),(0,[z0,z1,z3,z4,z115,z5,z234]),(0,[z66,z0,z1,z3,z4,z5,z86]),(0,[z0,z1,z3,z670,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z44]),(0,[z0,z1,z3,z179,z4,z5,z6])],[(0,[z0,z1,z8,z3,z4,z5,z44]),(0,[z0,z1,z3,z4,z5,z671,z6]),(0,[z0,z1,z3,z4,z5,z6,z672])],[(0,[z0,z673,z1,z3,z4,z5,z6]),(0,[z65,z1,z186,z3,z4,z5,z6]),(0,[z0,z1,z3,z148,z60,z5,z6]),(0,[z674,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z29,z29])],[(0,[z0,z1,z675,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z676,z5,z6]),(1,[z73,z1,z3,z4,z5,z268]),(0,[z0,z677,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z678,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z679]),(0,[z438,z0,z1,z3,z4,z5,z6]),(0,[z41,z75,z1,z3,z4,z5,z6]),(0,[z680,z0,z1,z3,z4,z5,z6]),(0,[z66,z0,z1,z3,z4,z5,z268]),(0,[z0,z1,z3,z4,z5,z6,z206]),(0,[z0,z1,z681,z3,z4,z5,z6]),(0,[z0,z1,z3,z682,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z635]),(0,[z0,z1,z3,z4,z5,z683,z6])],[(0,[z0,z1,z3,z33,z5,z257,z6]),(0,[z75,z0,z1,z3,z4,z5,z17]),(0,[z0,z684,z1,z3,z4,z5,z6]),(0,[z0,z1,z685,z3,z4,z5,z6])],[(0,[z0,z1,z3,z686,z4,z5,z6]),(0,[z687,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z213]),(0,[z0,z1,z688,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z6]),(0,[z0,z37,z1,z3,z4,z5,z101])],[(0,[z0,z689,z1,z3,z4,z5,z6]),(0,[z0,z1,z690,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z17,z45])],[(0,[z232,z0,z28,z3,z4,z5,z6]),(0,[z32,z232,z1,z3,z4,z5,z6]),(0,[z0,z1,z691,z3,z4,z5,z6]),(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z140,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z109,z6]),(0,[z0,z1,z3,z120,z4,z5,z17])],[(0,[z69,z0,z1,z3,z4,z5,z29]),(0,[z0,z89,z1,z132,z4,z5,z6]),(0,[z0,z693,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z294]),(0,[z0,z1,z3,z4,z561,z5,z29])],[(1,[z32,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z694]),(0,[z0,z1,z3,z4,z5,z695,z6]),(0,[z0,z1,z3,z4,z696,z5,z6]),(1,[z0,z1,z48,z3,z4,z45])],[(0,[z0,z1,z3,z120,z9,z5,z6]),(0,[z0,z89,z1,z3,z4,z5,z29]),(0,[z0,z1,z48,z3,z67,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z697,z5,z6]),(0,[z0,z1,z3,z4,z5,z135,z6]),(0,[z0,z1,z3,z4,z5,z616,z6]),(0,[z0,z1,z3,z4,z698,z5,z6])],[(0,[z0,z1,z3,z4,z699,z5,z6]),(0,[z0,z1,z3,z4,z700,z5,z6])],[(0,[z83,z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z701,z5,z6]),(0,[z570,z0,z1,z3,z4,z5,z29])],[(0,[z38,z0,z1,z3,z4,z317,z6]),(0,[z0,z1,z3,z4,z107,z55,z6]),(0,[z0,z1,z3,z4,z5,z6,z108]),(1,[z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z702,z5,z6])],[(0,[z0,z1,z3,z4,z34,z68,z6]),(0,[z0,z1,z3,z4,z5,z703,z6])],[(0,[z0,z286,z1,z3,z4,z5,z6]),(0,[z0,z1,z479,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z86,z6])],[(0,[z13,z0,z1,z3,z4,z5,z6]),(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z704,z6]),(1,[z0,z1,z3,z67,z5,z257]),(0,[z0,z1,z3,z67,z4,z162,z5])],[(0,[z705,z0,z1,z3,z4,z5,z6]),(0,[z13,z260,z1,z3,z4,z5,z6]),(0,[z0,z89,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z706]),(0,[z0,z151,z1,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z707,z5,z6]),(0,[z0,z1,z3,z4,z5,z708]),(0,[z0,z1,z178,z3,z140,z6]),(0,[z0,z1,z3,z4,z6,z709]),(0,[z0,z3,z4,z5,z29,z710])],[(0,[z0,z1,z3,z711,z5,z6]),(0,[z399,z1,z3,z9,z5,z6]),(0,[z712,z1,z3,z4,z5,z6]),(0,[z713,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z374,z4,z5]),(0,[z75,z1,z445,z3,z4,z6]),(0,[z0,z1,z642,z4,z5,z29]),(0,[z0,z1,z3,z714,z5,z6]),(0,[z0,z715,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z716,z6]),(0,[z11,z12,z3,z4,z55,z6]),(0,[z0,z1,z644,z4,z5,z29])],[(0,[z232,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z65,z1,z153,z4,z5,z6]),(0,[z379,z1,z3,z4,z5,z20]),(0,[z0,z1,z3,z718,z4,z5])],[(0,[z13,z0,z14,z4,z5,z17]),(0,[z0,z1,z221,z4,z107,z161])],[(0,[z0,z151,z3,z4,z669,z6]),(0,[z0,z1,z3,z4,z719,z6]),(0,[z36,z0,z184,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z720]),(0,[z0,z1,z3,z4,z5,z721]),(0,[z0,z3,z4,z5,z722,z6])],[(0,[z0,z1,z530,z4,z5,z29]),(0,[z0,z1,z4,z723,z5,z6]),(0,[z0,z1,z3,z4,z138,z102]),(0,[z515,z1,z3,z4,z5,z81])]],
   [[(0,[z36,z0,z339,z3,z4,z5]),(0,[z12,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z724]),(0,[z0,z1,z47,z723,z5,z6]),(0,[z0,z1,z330,z3,z5,z108])],[(0,[z0,z1,z3,z4,z725,z6]),(1,[z1,z3,z726,z5,z6]),(0,[z0,z1,z3,z4,z5,z727]),(0,[z260,z89,z3,z4,z5,z6])],[(0,[z41,z1,z3,z4,z115,z209]),(0,[z0,z1,z3,z4,z5,z728]),(0,[z0,z1,z47,z140,z5,z508])],[(0,[z0,z1,z3,z729,z5,z6]),(0,[z0,z1,z3,z4,z5,z730]),(0,[z0,z1,z3,z731,z5,z6]),(0,[z0,z1,z732,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z733]),(0,[z0,z1,z3,z4,z734,z6])],[(0,[z0,z1,z3,z4,z5,z735]),(0,[z0,z1,z3,z125,z317,z6]),(0,[z0,z100,z8,z3,z4,z5]),(0,[z0,z1,z3,z5,z736,z6]),(0,[z0,z1,z3,z67,z5,z737])],[(0,[z0,z1,z738,z4,z5,z6]),(0,[z1,z28,z178,z3,z4,z6])],[(0,[z84,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z72,z5,z17]),(0,[z0,z739,z3,z4,z5,z6])]],
   [[(0,[z176,z0,z1,z3,z4,z5]),(0,[z1,z28,z3,z251,z5,z6]),(0,[z0,z1,z3,z4,z5,z740]),(0,[z0,z741,z3,z4,z5,z6]),(0,[z651,z1,z3,z33,z5,z6])],[(0,[z0,z1,z3,z4,z5,z742]),(0,[z41,z1,z3,z4,z115,z234]),(0,[z743,z1,z3,z4,z5,z6]),(0,[z0,z1,z744,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z745]),(0,[z0,z1,z3,z4,z5,z746]),(0,[z0,z1,z47,z140,z138,z6]),(0,[z0,z1,z3,z120,z171,z6])],[(0,[z0,z1,z3,z4,z747,z5]),(0,[z0,z1,z249,z3,z4,z5]),(0,[z0,z1,z3,z120,z208,z6]),(0,[z748,z96,z1,z3,z4,z5]),(0,[z0,z1,z3,z749,z4,z5])],[(0,[z0,z1,z3,z4,z5,z750])],[(0,[z0,z1,z3,z4,z751,z6]),(0,[z0,z1,z3,z4,z5,z752]),(0,[z38,z1,z39,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z753]),(0,[z41,z1,z3,z226,z4,z6]),(0,[z0,z1,z3,z4,z5,z754]),(0,[z0,z1,z3,z755,z5,z6]),(0,[z1,z3,z4,z5,z6,z756])],[(0,[z396,z28,z3,z4,z5,z6]),(0,[z65,z1,z186,z4,z5,z195]),(0,[z75,z1,z3,z4,z34,z17]),(0,[z0,z1,z3,z4,z5,z757]),(0,[z0,z1,z3,z4,z5,z206]),(0,[z0,z1,z758,z3,z4,z5])],[(0,[z0,z759,z3,z4,z5,z6]),(0,[z0,z1,z3,z374,z307,z5]),(0,[z0,z1,z3,z4,z5,z209]),(0,[z96,z3,z4,z55,z5,z6]),(0,[z0,z1,z3,z5,z17,z760])],[(0,[z0,z99,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z213]),(0,[z0,z1,z3,z4,z5,z635]),(0,[z0,z1,z3,z4,z5,z761]),(0,[z0,z1,z3,z762,z5,z6])]],
   [[(0,[z38,z104,z39,z4,z5,z6]),(0,[z0,z1,z3,z763,z251,z5]),(0,[z260,z1,z3,z4,z5,z213])],[(0,[z66,z1,z3,z4,z5,z70]),(0,[z0,z1,z3,z4,z5,z764])],[(0,[z0,z1,z3,z72,z114,z6]),(0,[z765,z1,z3,z4,z5,z6]),(0,[z766,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z767])],[(0,[z232,z1,z178,z3,z4,z6]),(0,[z104,z3,z39,z4,z5,z6]),(0,[z0,z1,z768,z3,z4,z6]),(0,[z0,z1,z769,z3,z4,z5])],[(0,[z0,z770,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z771]),(0,[z0,z1,z46,z148,z5,z29])],[(0,[z0,z1,z3,z4,z5,z772]),(0,[z0,z183,z3,z4,z5,z17]),(0,[z0,z1,z3,z125,z5,z17]),(0,[z32,z1,z3,z9,z5,z6]),(0,[z0,z1,z3,z4,z5,z773]),(0,[z0,z1,z3,z4,z5,z234]),(0,[z0,z1,z3,z170,z5,z17]),(0,[z0,z1,z3,z4,z199,z17]),(0,[z0,z1,z48,z3,z4,z45])],[(0,[z0,z774,z3,z4,z5,z6]),(0,[z1,z3,z4,z775,z5,z6]),(0,[z13,z0,z744,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z776]),(0,[z0,z1,z3,z4,z5,z777]),(0,[z778,z1,z3,z4,z5,z6]),(0,[z779,z1,z3,z4,z5,z6]),(0,[z0,z1,z221,z155,z107,z6])],[(0,[z0,z1,z3,z4,z780,z6]),(0,[z0,z1,z781,z3,z5,z209]),(0,[z0,z1,z3,z4,z5,z782]),(0,[z0,z1,z3,z4,z5,z783]),(0,[z0,z1,z141,z4,z5,z767]),(0,[z784,z0,z3,z4,z5,z17])]],
   [[(0,[z13,z0,z14,z4,z5,z29]),(0,[z0,z37,z3,z4,z5,z722])],[(0,[z0,z785,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z786]),(0,[z0,z1,z3,z4,z787,z6]),(0,[z0,z1,z278,z3,z4,z45])],[(0,[z0,z1,z3,z788,z5,z6]),(0,[z0,z1,z3,z4,z5,z789]),(0,[z426,z1,z3,z4,z115,z6]),(0,[z0,z1,z3,z127,z122,z6]),(0,[z790,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z120,z251,z6]),(0,[z13,z379,z14,z4,z5,z6]),(0,[z13,z0,z14,z4,z199,z6]),(0,[z0,z744,z14,z4,z5,z6]),(0,[z0,z1,z3,z791,z5,z6]),(0,[z0,z1,z3,z792,z5,z6]),(0,[z0,z1,z3,z793,z223,z6])],[(0,[z0,z1,z794,z4,z5,z6]),(0,[z0,z1,z200,z3,z251,z6]),(0,[z0,z89,z132,z4,z5,z230])],[(0,[z232,z402,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z795,z6]),(0,[z0,z1,z3,z4,z796,z6]),(0,[z36,z0,z100,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z797]),(0,[z0,z1,z3,z67,z5,z257])],[(0,[z0,z1,z3,z798,z5,z6]),(0,[z0,z1,z3,z4,z799,z6])],[(0,[z38,z183,z39,z4,z5,z6]),(0,[z0,z1,z3,z800,z5,z6]),(0,[z0,z1,z3,z4,z5,z801])]],
   [[(0,[z0,z1,z3,z4,z802,z6]),(0,[z0,z1,z3,z125,z114,z6]),(0,[z0,z1,z3,z4,z6,z803]),(0,[z0,z1,z3,z4,z804,z6]),(0,[z0,z1,z3,z374,z421,z4]),(0,[z13,z0,z14,z4,z5,z6]),(0,[z805,z1,z3,z4,z5,z6])],[(0,[z41,z1,z3,z4,z775,z6])],[(0,[z0,z1,z3,z72,z5,z29]),(0,[z0,z1,z3,z806,z5,z6]),(0,[z0,z1,z3,z5,z29,z289])],[(0,[z0,z1,z178,z3,z251,z6]),(0,[z0,z151,z3,z4,z207,z6]),(0,[z0,z1,z4,z5,z17,z364])],[(0,[z38,z1,z39,z4,z5,z6]),(0,[z0,z104,z3,z125,z5,z6]),(0,[z0,z15,z3,z16,z5,z262]),(0,[z0,z1,z3,z807,z5,z6]),(0,[z0,z1,z3,z4,z808,z17]),(0,[z809,z1,z3,z4,z5,z6])],[(0,[z0,z1,z810,z3,z5,z6]),(0,[z0,z1,z3,z811,z4,z5]),(0,[z0,z183,z3,z72,z5,z6]),(0,[z0,z812,z3,z4,z5,z6]),(0,[z0,z1,z813,z3,z251,z5]),(0,[z0,z1,z4,z5,z17,z542]),(0,[z379,z1,z3,z127,z5,z6]),(0,[z0,z1,z3,z4,z814,z6]),(0,[z815,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z816,z5,z6]),(0,[z11,z0,z3,z4,z55,z6]),(0,[z817,z1,z3,z4,z5,z6])],[(0,[z232,z557,z3,z4,z5,z6]),(0,[z136,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z818,z5,z6]),(0,[z0,z1,z457,z4,z68,z6]),(0,[z0,z1,z3,z4,z5,z61]),(0,[z84,z1,z3,z4,z5,z17]),(1,[z0,z3,z819,z5,z6]),(0,[z0,z1,z3,z4,z5,z820])]],
   [[(0,[z0,z1,z821,z4,z5,z6]),(0,[z0,z1,z822,z3,z4,z5]),(0,[z75,z1,z3,z4,z34,z29]),(0,[z0,z1,z3,z823,z5,z6]),(1,[z0,z1,z723,z5,z6])],[(0,[z0,z1,z3,z4,z5,z824]),(0,[z73,z1,z3,z4,z5,z476]),(0,[z0,z1,z3,z4,z5,z825])],[(0,[z0,z286,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z826]),(0,[z0,z1,z3,z4,z5,z827]),(0,[z0,z1,z3,z4,z5,z828]),(0,[z0,z99,z3,z4,z5,z29]),(0,[z0,z829,z3,z4,z5,z6]),(0,[z830,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z831]),(0,[z0,z1,z3,z5,z6,z832])],[(0,[z0,z1,z3,z833,z5,z6]),(0,[z0,z1,z3,z4,z5,z834]),(0,[z0,z1,z835,z3,z4,z5]),(1,[z1,z3,z4,z775,z6]),(0,[z0,z1,z3,z5,z832,z209]),(0,[z0,z1,z836,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z837]),(1,[z1,z3,z4,z5,z838]),(0,[z839,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z840]),(0,[z0,z1,z3,z4,z841,z6]),(0,[z0,z1,z394,z140,z5,z6])],[(0,[z0,z1,z842,z3,z4,z5]),(1,[z1,z843,z4,z5,z6]),(0,[z367,z1,z3,z9,z5,z6]),(0,[z0,z844,z3,z4,z5,z29])],[(0,[z0,z1,z3,z845,z5,z6]),(0,[z0,z1,z3,z4,z5,z846]),(0,[z0,z1,z3,z4,z847,z6]),(0,[z0,z1,z3,z848,z5,z6]),(0,[z0,z1,z3,z4,z5,z849])]],
   [[(0,[z0,z183,z3,z4,z5,z29]),(0,[z0,z1,z249,z3,z421,z4]),(0,[z75,z1,z3,z4,z34,z6]),(0,[z0,z1,z3,z170,z5,z29]),(0,[z0,z1,z3,z4,z199,z29]),(0,[z0,z1,z4,z850,z68,z6])],[(0,[z96,z1,z3,z4,z5,z6]),(0,[z0,z1,z851,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z852]),(0,[z75,z1,z3,z503,z34,z6]),(0,[z853,z1,z3,z4,z5,z6]),(0,[z0,z1,z854,z3,z4,z5]),(0,[z0,z1,z227,z3,z5,z17])],[(0,[z75,z1,z3,z4,z775,z6])],[(0,[z69,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z855,z5,z6]),(0,[z0,z183,z3,z125,z5,z6]),(0,[z0,z1,z3,z856,z5,z6]),(0,[z0,z15,z3,z819,z5,z6]),(0,[z0,z1,z47,z140,z79,z6])],[(0,[z386,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z110]),(0,[z0,z1,z3,z4,z122,z20]),(0,[z857,z1,z3,z4,z5,z6]),(0,[z858,z1,z3,z4,z5,z6])],[(0,[z0,z859,z3,z4,z5,z6]),(0,[z0,z132,z744,z4,z5,z6]),(0,[z0,z1,z3,z860,z5,z6]),(0,[z0,z715,z3,z4,z5,z29])],[(0,[z65,z1,z186,z4,z5,z110]),(0,[z0,z100,z3,z4,z5,z45]),(0,[z0,z1,z3,z4,z5,z861])],[(0,[z232,z27,z3,z4,z5,z29]),(0,[z0,z1,z3,z862,z5,z6]),(0,[z0,z1,z3,z863,z4,z5]),(0,[z0,z416,z3,z4,z5,z44]),(0,[z0,z1,z3,z4,z5,z864]),(0,[z0,z1,z3,z4,z162,z393])]],
   [[(0,[z0,z1,z3,z125,z5,z6]),(0,[z0,z1,z3,z318,z5,z6]),(0,[z157,z0,z3,z4,z5,z44]),(0,[z0,z1,z3,z155,z68,z6]),(0,[z0,z1,z19,z4,z5,z17]),(0,[z0,z1,z8,z3,z5,z737]),(0,[z0,z1,z3,z4,z162,z451])],[(0,[z260,z1,z3,z318,z5,z6]),(0,[z0,z89,z132,z4,z5,z6]),(0,[z0,z1,z3,z5,z865,z29])],[(0,[z506,z0,z14,z4,z5,z6]),(0,[z438,z1,z3,z374,z33,z5]),(0,[z0,z1,z47,z140,z5,z6])],[(0,[z866,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z867]),(0,[z0,z1,z868,z4,z5,z6]),(0,[z0,z1,z3,z67,z307,z5]),(0,[z0,z1,z3,z819,z5,z6])],[(0,[z0,z1,z3,z869,z5,z6]),(0,[z1,z3,z726,z33,z5,z6]),(0,[z0,z1,z3,z870,z5,z6]),(0,[z66,z0,z1,z227,z3,z5])],[(0,[z0,z1,z871,z3,z4,z5]),(0,[z0,z1,z48,z3,z4,z142])],[(0,[z73,z286,z3,z4,z5,z268]),(0,[z0,z1,z3,z4,z5,z872]),(0,[z0,z1,z3,z4,z5,z873]),(0,[z0,z1,z200,z479,z3,z223])],[(0,[z0,z1,z3,z4,z874,z6]),(0,[z0,z1,z3,z4,z5,z875]),(0,[z0,z1,z597,z4,z5,z29]),(0,[z0,z1,z876,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z877]),(0,[z0,z1,z3,z127,z5,z20]),(0,[z0,z878,z3,z4,z5,z6])],[(0,[z505,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z879,z5,z6]),(0,[z0,z1,z314,z4,z5,z29]),(0,[z0,z1,z3,z4,z122,z6]),(0,[z0,z1,z3,z5,z6,z865]),(0,[z0,z1,z3,z4,z880,z6]),(0,[z0,z1,z3,z4,z5,z881]),(0,[z0,z1,z3,z4,z882,z17]),(0,[z0,z1,z3,z4,z162,z883])],[(0,[z0,z1,z884,z3,z4,z5]),(0,[z0,z1,z3,z4,z885,z5]),(0,[z260,z1,z3,z4,z122,z6]),(0,[z0,z1,z3,z4,z5,z886]),(0,[z84,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z887]),(0,[z0,z1,z4,z492,z5,z29])],[(0,[z0,z1,z3,z4,z5,z888]),(0,[z0,z1,z3,z4,z5,z889]),(0,[z890,z1,z3,z4,z5,z6]),(0,[z0,z151,z3,z4,z207,z17]),(0,[z0,z1,z891,z3,z5,z6])],[(0,[z38,z1,z39,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z892]),(0,[z0,z1,z330,z3,z5,z59])],[(0,[z0,z893,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z722,z101]),(0,[z0,z1,z3,z4,z5,z894]),(0,[z895,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z896]),(0,[z674,z1,z3,z4,z34,z6]),(0,[z0,z1,z3,z4,z897,z6]),(0,[z11,z0,z3,z4,z55,z17]),(0,[z0,z1,z3,z5,z6,z760]),(0,[z0,z1,z3,z4,z5,z737])],[(0,[z73,z0,z1,z227,z3,z5]),(0,[z0,z1,z3,z4,z808,z6]),(0,[z0,z1,z3,z4,z898,z29])]],
   [[(0,[z899,z0,z1,z3,z4,z5]),(0,[z0,z1,z8,z3,z5,z694]),(0,[z0,z1,z3,z4,z900,z6]),(0,[z901,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z793,z6])],[(0,[z0,z1,z3,z902,z5,z6]),(0,[z0,z1,z3,z4,z903,z6]),(0,[z0,z1,z178,z3,z148,z6]),(0,[z0,z660,z3,z4,z5,z44]),(0,[z0,z1,z4,z5,z17,z29])],[(0,[z438,z1,z249,z3,z33,z5]),(0,[z0,z286,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z904])],[(0,[z0,z15,z3,z16,z5,z6])],[(0,[z379,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z905,z6]),(0,[z27,z906,z3,z4,z5,z6]),(0,[z0,z37,z100,z3,z4,z5]),(0,[z0,z1,z227,z3,z5,z29])],[(0,[z0,z1,z3,z4,z199,z213]),(0,[z0,z1,z152,z4,z5,z17]),(0,[z0,z1,z3,z4,z86,z883])],[(0,[z0,z1,z3,z4,z5,z195]),(0,[z1,z3,z4,z5,z70,z838]),(0,[z260,z1,z3,z127,z5,z6]),(0,[z0,z1,z3,z4,z5,z907]),(0,[z0,z1,z3,z4,z138,z508]),(0,[z0,z1,z3,z4,z5,z908]),(0,[z0,z1,z3,z4,z5,z909])],[(0,[z66,z1,z3,z170,z5,z70]),(0,[z0,z1,z3,z4,z5,z910])]],
   [[(0,[z0,z1,z3,z4,z317,z342]),(0,[z0,z3,z4,z911,z5,z6]),(0,[z32,z1,z3,z9,z5,z29]),(0,[z0,z1,z3,z4,z5,z912]),(0,[z0,z1,z3,z4,z913,z6]),(0,[z0,z1,z3,z4,z5,z914]),(0,[z0,z1,z3,z4,z5,z915])],[(0,[z0,z1,z3,z916,z5,z6]),(0,[z99,z3,z4,z115,z5,z6]),(0,[z0,z1,z3,z917,z5,z6]),(0,[z96,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z918])],[(0,[z0,z89,z744,z4,z5,z6]),(0,[z0,z15,z3,z16,z5,z326]),(0,[z919,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z348,z86]),(0,[z0,z1,z23,z4,z68,z17])],[(0,[z69,z28,z3,z4,z5,z17]),(0,[z0,z3,z4,z819,z5,z6]),(0,[z0,z1,z3,z4,z5,z920]),(0,[z0,z1,z221,z4,z107,z17]),(0,[z0,z1,z921,z3,z4,z5])],[(0,[z38,z1,z39,z72,z5,z6]),(0,[z0,z922,z3,z4,z5,z6]),(0,[z923,z1,z3,z4,z5,z6]),(0,[z0,z1,z227,z3,z5,z6])],[(0,[z0,z1,z177,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z924]),(0,[z11,z96,z3,z4,z55,z6]),(0,[z0,z1,z723,z148,z5,z6]),(0,[z0,z1,z625,z148,z5,z6])],[(0,[z455,z28,z3,z4,z5,z6]),(0,[z0,z1,z375,z4,z5,z29]),(0,[z0,z1,z3,z4,z925,z6]),(0,[z0,z1,z3,z4,z5,z926])],[(0,[z0,z1,z3,z4,z5,z927]),(0,[z0,z1,z3,z928,z5,z6]),(0,[z0,z1,z3,z929,z5,z6]),(0,[z0,z1,z3,z4,z5,z930])]],
   [[(0,[z0,z1,z931,z3,z4,z5]),(0,[z232,z1,z3,z251,z5,z6]),(0,[z0,z1,z3,z932,z5,z6]),(0,[z0,z1,z3,z318,z5,z17]),(0,[z0,z1,z227,z3,z5,z101]),(0,[z0,z1,z46,z148,z5,z128])],[(0,[z0,z1,z3,z4,z5,z933]),(0,[z0,z89,z132,z4,z5,z17]),(0,[z934,z96,z1,z3,z4,z5]),(0,[z0,z1,z8,z3,z5,z58])],[(0,[z0,z1,z3,z4,z5,z935]),(0,[z1,z3,z4,z5,z838,z268]),(0,[z0,z1,z47,z140,z5,z17]),(0,[z0,z1,z3,z60,z6,z360])],[(0,[z0,z1,z3,z4,z5,z936]),(0,[z0,z3,z16,z819,z5,z6]),(0,[z0,z1,z604,z4,z5,z29]),(0,[z0,z1,z221,z4,z107,z460]),(0,[z0,z1,z200,z479,z3,z5])],[(0,[z0,z1,z3,z937,z5,z6])],[(0,[z0,z1,z3,z421,z4,z6]),(0,[z0,z1,z3,z4,z5,z938]),(0,[z0,z1,z3,z4,z5,z939]),(0,[z0,z1,z3,z5,z6,z737])],[(0,[z0,z1,z3,z940,z4,z6]),(0,[z0,z1,z178,z3,z257,z6]),(0,[z0,z1,z3,z4,z941,z6]),(0,[z13,z0,z14,z318,z5,z6]),(0,[z0,z151,z3,z4,z207,z29]),(0,[z0,z1,z4,z5,z6,z767])],[(0,[z0,z1,z3,z4,z942,z5]),(0,[z38,z1,z39,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z943]),(0,[z0,z1,z3,z4,z850,z6])]],
   [[(0,[z0,z1,z3,z763,z4,z5]),(0,[z0,z3,z4,z944,z207,z6]),(0,[z815,z1,z3,z4,z5,z29])],[(0,[z0,z1,z3,z4,z5,z945]),(0,[z0,z1,z3,z4,z946,z6]),(0,[z0,z1,z947,z3,z4,z5]),(0,[z0,z1,z3,z4,z122,z17]),(0,[z11,z0,z3,z4,z55,z29]),(0,[z0,z1,z4,z5,z17,z672])],[(0,[z0,z100,z3,z4,z5,z6]),(0,[z38,z1,z39,z125,z5,z6]),(0,[z73,z1,z3,z4,z5,z81]),(0,[z0,z1,z3,z4,z5,z948]),(0,[z0,z151,z3,z4,z207,z135]),(0,[z0,z1,z3,z4,z5,z949]),(0,[z0,z1,z4,z5,z767,z29])],[(0,[z0,z1,z3,z4,z5,z950]),(0,[z0,z951,z3,z4,z5,z6]),(0,[z0,z1,z221,z384,z107,z6]),(0,[z0,z1,z891,z3,z5,z17]),(1,[z0,z1,z3,z5,z737])],[(0,[z0,z1,z3,z4,z882,z6]),(0,[z0,z1,z3,z4,z952,z6]),(0,[z0,z1,z3,z155,z5,z161])],[(0,[z0,z286,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z953,z6]),(0,[z0,z1,z3,z4,z5,z954]),(0,[z157,z0,z3,z4,z5,z458])],[(0,[z232,z906,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z481,z86]),(0,[z955,z1,z3,z4,z5,z6]),(0,[z0,z89,z132,z4,z5,z61]),(0,[z83,z0,z3,z819,z5,z6])],[(0,[z92,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z956])]],
   [[(0,[z0,z1,z3,z957,z4,z5]),(0,[z0,z1,z3,z4,z6,z958]),(0,[z0,z1,z3,z4,z959,z6]),(0,[z66,z1,z3,z4,z5,z838]),(0,[z66,z1,z3,z4,z5,z308]),(0,[z260,z1,z3,z4,z5,z20]),(0,[z1,z3,z4,z5,z29,z756]),(0,[z0,z1,z48,z3,z4,z883])],[(0,[z0,z1,z3,z4,z5,z960]),(0,[z0,z1,z3,z4,z5,z961]),(0,[z962,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z963])],[(0,[z0,z1,z489,z4,z5,z17]),(0,[z0,z1,z8,z3,z5,z123]),(0,[z0,z1,z200,z3,z255,z6]),(0,[z0,z1,z3,z667,z60,z6]),(0,[z0,z1,z3,z5,z6,z964])],[(0,[z0,z1,z3,z4,z5,z965]),(0,[z0,z1,z3,z4,z5,z966]),(0,[z0,z1,z3,z4,z114,z342]),(0,[z0,z1,z3,z4,z5,z967]),(0,[z0,z1,z3,z968,z5,z6]),(0,[z0,z15,z3,z16,z5,z17]),(0,[z0,z1,z3,z4,z5,z74]),(0,[z969,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z970,z4,z5])],[(0,[z379,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z971,z6]),(0,[z96,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z79,z102])],[(0,[z0,z1,z3,z4,z5,z972]),(0,[z0,z1,z23,z4,z68,z24])],[(0,[z69,z28,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z973]),(0,[z0,z1,z659,z4,z5,z29]),(0,[z0,z1,z3,z384,z5,z161]),(0,[z0,z1,z221,z4,z107,z29])],[(0,[z0,z104,z3,z4,z5,z342]),(0,[z0,z1,z178,z8,z3,z6]),(0,[z0,z974,z3,z4,z5,z6]),(0,[z0,z1,z975,z3,z4,z5]),(0,[z0,z1,z8,z3,z5,z150])]],
   [[(0,[z0,z104,z3,z4,z317,z6]),(0,[z0,z976,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z561,z393]),(0,[z0,z1,z227,z3,z162,z5])],[(0,[z0,z1,z3,z4,z5,z977])],[(0,[z978,z0,z1,z3,z4,z5]),(0,[z0,z1,z306,z148,z5,z6]),(0,[z0,z1,z3,z4,z775,z6]),(0,[z0,z1,z3,z4,z6,z898])],[(0,[z0,z1,z3,z125,z5,z29]),(0,[z73,z1,z3,z4,z5,z838]),(0,[z117,z1,z3,z4,z5,z268]),(0,[z0,z1,z3,z318,z5,z29]),(0,[z0,z1,z3,z4,z5,z979]),(0,[z0,z1,z3,z4,z5,z102]),(0,[z0,z980,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z981,z29])],[(0,[z64,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z982,z6]),(0,[z0,z1,z3,z4,z5,z983]),(0,[z0,z1,z843,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z984]),(0,[z0,z1,z3,z4,z5,z985]),(0,[z0,z1,z3,z4,z246,z45]),(0,[z316,z1,z3,z4,z5,z70]),(0,[z0,z89,z132,z4,z5,z29]),(1,[z0,z3,z4,z5,z722])],[(0,[z355,z1,z3,z33,z5,z6]),(0,[z0,z1,z813,z3,z4,z5]),(0,[z0,z1,z47,z140,z5,z29]),(0,[z0,z1,z23,z4,z68,z6])],[(0,[z73,z100,z3,z4,z5,z268]),(0,[z0,z1,z3,z318,z199,z6]),(0,[z0,z1,z3,z986,z5,z6]),(0,[z0,z1,z3,z4,z5,z987]),(0,[z0,z1,z221,z4,z107,z6])],[(0,[z0,z1,z3,z4,z5,z988]),(0,[z1,z3,z989,z4,z5,z6]),(0,[z0,z1,z3,z5,z257,z737])]],
   [[(0,[z0,z1,z990,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z991]),(0,[z13,z0,z14,z4,z5,z213]),(0,[z0,z1,z3,z4,z5,z992]),(0,[z0,z3,z4,z5,z993,z6]),(0,[z0,z1,z3,z4,z79,z508]),(0,[z0,z1,z140,z723,z5,z6])],[(0,[z0,z1,z3,z4,z994,z6]),(0,[z0,z1,z3,z4,z5,z128]),(0,[z0,z1,z3,z4,z5,z995]),(0,[z0,z1,z3,z179,z5,z562])],[(0,[z0,z996,z3,z4,z5,z6]),(0,[z0,z1,z3,z997,z5,z6]),(0,[z0,z998,z3,z4,z5,z6]),(0,[z0,z1,z3,z999,z5,z6]),(0,[z1000,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1001,z6]),(0,[z438,z1,z3,z726,z5,z6]),(0,[z0,z1002,z3,z4,z5,z6]),(0,[z0,z1,z227,z48,z3,z5])],[(0,[z0,z89,z313,z4,z5,z6]),(0,[z0,z1,z3,z4,z122,z29])],[(0,[z0,z1,z3,z4,z5,z1003]),(0,[z0,z1,z3,z421,z4,z17]),(0,[z0,z1,z3,z4,z5,z1004]),(0,[z0,z1,z3,z120,z60,z6])],[(0,[z0,z183,z3,z4,z5,z342])],[(0,[z0,z1,z3,z4,z5,z1005]),(0,[z0,z1,z3,z4,z5,z508]),(0,[z0,z1,z23,z4,z850,z6])]],
   [[(1,[z906,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1006]),(0,[z1,z3,z843,z4,z5,z6]),(0,[z41,z42,z3,z4,z115,z6]),(0,[z1007,z1,z3,z4,z5,z6]),(0,[z0,z1,z1008,z3,z4,z6])],[(0,[z106,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1009]),(0,[z1,z3,z4,z5,z6,z981]),(0,[z0,z1,z3,z4,z5,z161])],[(0,[z0,z1,z3,z4,z1010,z6]),(0,[z0,z100,z3,z4,z5,z17]),(0,[z0,z1,z4,z485,z5,z29])],[(0,[z0,z1,z3,z4,z5,z342]),(0,[z0,z1,z3,z4,z5,z1011]),(0,[z0,z1,z3,z4,z5,z1012])],[(0,[z0,z1,z3,z4,z317,z6]),(0,[z0,z112,z3,z4,z5,z233])],[(0,[z0,z1,z3,z4,z317,z311]),(0,[z0,z1,z3,z1013,z4,z5]),(0,[z0,z1,z3,z1014,z5,z6]),(0,[z0,z151,z3,z4,z944,z6]),(0,[z36,z0,z3,z4,z5,z57]),(0,[z0,z1,z354,z3,z5,z58])],[(0,[z0,z1,z1015,z3,z4,z6]),(0,[z0,z15,z3,z16,z5,z29]),(0,[z0,z1,z3,z5,z6,z1016]),(0,[z0,z1,z3,z4,z138,z6]),(0,[z0,z1,z1017,z4,z5,z6]),(0,[z0,z1,z3,z1018,z5,z6])],[(0,[z0,z1019,z3,z4,z5,z6]),(0,[z0,z1,z3,z1020,z5,z6]),(0,[z379,z1,z3,z4,z5,z29]),(0,[z1021,z1,z3,z4,z5,z6]),(0,[z83,z0,z3,z181,z5,z6])]],
   [[(0,[z0,z1,z8,z3,z374,z5]),(0,[z0,z1,z3,z120,z51,z6]),(0,[z0,z1,z3,z4,z5,z722]),(0,[z0,z1,z3,z4,z5,z1022]),(0,[z0,z1,z3,z1023,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1024]),(0,[z0,z1,z1025,z3,z4,z5]),(0,[z0,z1,z3,z1026,z5,z6]),(0,[z1027,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1028])],[(0,[z0,z1,z3,z726,z5,z6]),(0,[z0,z1,z3,z307,z5,z6]),(0,[z379,z1,z3,z4,z199,z6])],[(0,[z692,z1,z3,z33,z5,z6]),(0,[z0,z1,z3,z1029,z5,z6]),(0,[z73,z1,z681,z3,z4,z5]),(0,[z0,z1,z3,z127,z199,z6]),(0,[z1030,z1,z3,z4,z5,z6])],[(0,[z0,z42,z3,z4,z5,z6]),(0,[z0,z1,z3,z1031,z5,z6]),(0,[z0,z1,z3,z4,z1032,z6]),(0,[z1,z3,z726,z4,z5,z6]),(0,[z1,z3,z4,z775,z34,z6]),(0,[z0,z1033,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1034]),(0,[z0,z1,z3,z4,z5,z1035])],[(0,[z0,z1,z3,z4,z5,z1036]),(0,[z0,z1,z3,z1037,z4,z5]),(0,[z66,z1,z3,z4,z5,z309]),(0,[z0,z37,z3,z4,z5,z101]),(0,[z0,z1,z622,z4,z5,z29]),(0,[z0,z1,z581,z4,z5,z17]),(0,[z0,z1,z3,z5,z17,z289])],[(0,[z0,z1,z3,z4,z5,z1038]),(0,[z1,z186,z843,z4,z5,z6]),(0,[z0,z100,z3,z67,z4,z5]),(0,[z0,z1,z3,z4,z5,z1039])]],
   [[(0,[z328,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z127,z5,z6]),(0,[z0,z1,z3,z318,z5,z213]),(0,[z0,z1,z3,z4,z5,z262]),(0,[z1040,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z528,z29])],[(0,[z0,z1,z1041,z4,z5,z6]),(0,[z144,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z44,z722]),(0,[z0,z1,z3,z4,z1042,z6]),(0,[z0,z1,z8,z3,z5,z59])],[(0,[z0,z1,z3,z4,z1043,z6]),(0,[z0,z1,z3,z929,z5,z29]),(0,[z0,z1044,z3,z4,z5,z17])],[(0,[z0,z1,z178,z3,z4,z17]),(0,[z0,z1,z3,z932,z5,z29]),(0,[z0,z1,z8,z373,z3,z5]),(0,[z0,z1,z48,z3,z289,z45])],[(0,[z0,z1,z3,z4,z5,z1045]),(0,[z80,z0,z3,z4,z55,z6]),(0,[z0,z1,z419,z4,z5,z17]),(0,[z0,z1,z200,z3,z539,z6])],[(0,[z0,z1046,z3,z4,z5,z6]),(0,[z0,z1,z1047,z3,z4,z6]),(0,[z0,z1,z8,z3,z333,z5]),(0,[z0,z1,z3,z1048,z5,z6])],[(0,[z0,z1,z3,z67,z5,z562]),(0,[z0,z1,z227,z48,z3,z45])],[(0,[z0,z1,z3,z1049,z4,z5]),(0,[z0,z1,z3,z4,z5,z1050]),(0,[z0,z1,z479,z3,z4,z5])]],
   [[(0,[z0,z1,z4,z1051,z5,z6]),(0,[z0,z1052,z3,z4,z5,z6]),(0,[z0,z1,z3,z1053,z5,z6]),(0,[z0,z1,z3,z421,z4,z29]),(0,[z0,z1,z3,z4,z5,z1054]),(0,[z0,z1,z1055,z3,z5,z6]),(0,[z0,z3,z4,z5,z993,z17]),(0,[z0,z1,z4,z5,z17,z172])],[(0,[z0,z1,z3,z4,z122,z213]),(0,[z1056,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z230]),(0,[z0,z1,z3,z4,z1057,z6]),(0,[z0,z3,z4,z944,z5,z6]),(0,[z0,z1,z3,z155,z5,z6])],[(0,[z438,z1,z3,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z1058]),(0,[z0,z1,z200,z3,z223,z6]),(0,[z0,z1,z3,z4,z5,z883])],[(0,[z1,z3,z9,z726,z5,z6]),(0,[z0,z1,z1059,z3,z5,z6]),(0,[z0,z3,z4,z5,z6,z710]),(0,[z0,z1,z3,z4,z366,z86]),(0,[z0,z1,z200,z3,z392,z6])],[(0,[z0,z1,z3,z1060,z4,z6]),(0,[z438,z1,z3,z421,z33,z6]),(0,[z0,z100,z3,z4,z5,z29]),(0,[z0,z1,z3,z120,z60,z17])],[(0,[z0,z1061,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1062]),(0,[z0,z1,z3,z4,z5,z1063]),(0,[z0,z1,z76,z140,z5,z6]),(0,[z0,z1,z76,z4,z107,z6])],[(0,[z0,z1,z339,z3,z4,z5]),(0,[z0,z1,z4,z5,z850,z6]),(0,[z0,z1,z4,z5,z29,z633])]],
   [[(0,[z0,z1,z3,z4,z114,z311])],[(0,[z0,z1,z3,z4,z5,z1064]),(0,[z0,z1,z3,z4,z5,z1065]),(0,[z0,z1066,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1067,z6]),(0,[z0,z1,z178,z3,z223,z6]),(0,[z0,z1,z439,z4,z5,z17]),(0,[z36,z0,z3,z4,z5,z44])],[(0,[z0,z104,z3,z4,z5,z6]),(0,[z0,z1,z1068,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1069]),(0,[z0,z1,z1070,z4,z5,z6]),(0,[z0,z1,z3,z4,z1071,z6]),(0,[z0,z1,z3,z1072,z5,z6])],[(0,[z0,z1,z1073,z3,z4,z5]),(0,[z0,z1,z1074,z3,z4,z6]),(0,[z0,z1,z1075,z4,z5,z6]),(0,[z0,z104,z3,z4,z5,z311]),(0,[z0,z1,z3,z4,z317,z17]),(0,[z379,z1,z3,z4,z5,z213]),(0,[z0,z1,z3,z384,z5,z6]),(0,[z0,z1,z3,z155,z107,z6]),(0,[z962,z1,z3,z4,z5,z29]),(0,[z0,z1,z626,z4,z5,z17]),(0,[z0,z1,z3,z120,z793,z6])],[(0,[z0,z1,z3,z1076,z5,z6]),(0,[z66,z444,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z199,z20]),(0,[z0,z1,z4,z5,z29,z488]),(0,[z0,z1,z4,z5,z569,z29]),(0,[z0,z1,z200,z3,z793,z6])],[(0,[z0,z1,z1077,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z1078]),(0,[z0,z1,z3,z4,z138,z17]),(0,[z969,z1,z3,z4,z5,z29])],[(0,[z0,z1079,z3,z4,z5,z6]),(0,[z83,z0,z3,z181,z5,z17]),(0,[z0,z1,z1080,z3,z5,z6]),(0,[z0,z1,z3,z4,z6,z883])]],
   [[(0,[z0,z1,z1081,z3,z4,z6]),(0,[z0,z1,z3,z4,z1082,z6]),(0,[z0,z1,z3,z1023,z5,z17])],[(0,[z0,z1,z3,z1083,z5,z6]),(0,[z83,z84,z3,z181,z5,z6]),(0,[z0,z1,z479,z3,z60,z5])],[(0,[z0,z1,z3,z307,z5,z17]),(0,[z0,z1,z3,z4,z5,z20]),(0,[z13,z0,z14,z4,z122,z6]),(0,[z0,z1,z628,z4,z5,z29])],[(0,[z32,z1,z3,z248,z5,z6]),(0,[z38,z1,z843,z4,z5,z6]),(0,[z41,z1,z3,z4,z115,z6]),(0,[z0,z1,z3,z4,z1084,z6])],[(0,[z1,z906,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1085,z6]),(0,[z0,z1,z3,z4,z5,z1086]),(0,[z65,z1,z843,z4,z5,z6]),(0,[z0,z42,z3,z4,z5,z17]),(0,[z0,z1,z1087,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1088]),(0,[z0,z139,z3,z16,z5,z6])],[(0,[z467,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1089]),(0,[z38,z1,z39,z4,z5,z342]),(0,[z0,z1,z655,z148,z5,z6]),(0,[z117,z1,z3,z4,z5,z187])],[(0,[z0,z1,z3,z4,z1090,z6]),(0,[z0,z1,z178,z3,z4,z29]),(0,[z0,z424,z3,z4,z5,z422])],[(0,[z1091,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z24]),(0,[z35,z0,z3,z4,z5,z57]),(0,[z0,z1,z3,z60,z793,z6])]],
   [[(0,[z0,z1,z3,z1092,z5,z6]),(0,[z0,z1,z3,z1093,z4,z5]),(0,[z0,z1,z3,z4,z5,z1094]),(0,[z0,z1,z1095,z4,z5,z6]),(0,[z0,z1,z3,z127,z5,z17]),(0,[z0,z1,z1096,z3,z4,z5]),(0,[z0,z1,z3,z4,z79,z6]),(0,[z0,z1,z23,z4,z68,z29]),(0,[z0,z1,z3,z4,z162,z86])],[(0,[z69,z176,z28,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1097]),(0,[z0,z1,z3,z4,z5,z1098]),(0,[z0,z1,z8,z3,z307,z5]),(0,[z144,z1,z3,z4,z5,z17]),(0,[z83,z144,z3,z181,z5,z6]),(0,[z0,z1,z3,z4,z1099,z6])],[(0,[z0,z27,z3,z4,z5,z206]),(0,[z0,z1,z3,z4,z5,z1100]),(0,[z0,z1,z1101,z3,z4,z5]),(0,[z1,z3,z989,z4,z5,z29]),(0,[z0,z1102,z3,z4,z5,z6])],[(0,[z28,z3,z290,z4,z5,z6]),(0,[z0,z183,z3,z4,z5,z311]),(0,[z0,z1,z3,z72,z5,z342]),(0,[z1027,z144,z1,z3,z4,z5]),(0,[z0,z1,z563,z3,z4,z142]),(0,[z0,z1,z3,z391,z5,z257])],[(0,[z0,z1103,z3,z4,z5,z6]),(0,[z260,z3,z14,z4,z5,z6])],[(0,[z0,z1,z3,z1104,z5,z6]),(0,[z0,z1044,z3,z4,z5,z6]),(0,[z0,z1,z479,z3,z9,z5]),(0,[z0,z100,z3,z4,z5,z86]),(0,[z0,z1,z3,z1048,z5,z17]),(0,[z0,z1,z200,z3,z217,z223]),(0,[z0,z1,z3,z4,z5,z1105])],[(0,[z0,z1,z3,z4,z5,z1106]),(0,[z0,z1,z3,z4,z1107,z6]),(0,[z0,z1,z178,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1108]),(0,[z0,z1,z3,z4,z5,z838]),(0,[z13,z0,z14,z127,z5,z6]),(0,[z0,z1,z46,z148,z5,z17])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1109,z3,z4,z5,z6]),(0,[z0,z1,z10,z4,z107,z6]),(0,[z1110,z1,z3,z4,z5,z6])]],
   [[(0,[z260,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z311]),(0,[z0,z1,z3,z503,z5,z6]),(0,[z0,z1,z3,z251,z5,z6]),(0,[z0,z1,z3,z1111,z5,z6]),(0,[z1112,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z60,z29])],[(0,[z65,z1,z186,z4,z5,z6]),(0,[z0,z1,z3,z148,z79,z6])],[(0,[z0,z1,z3,z4,z5,z1113]),(0,[z0,z28,z3,z4,z5,z206]),(0,[z529,z0,z3,z181,z5,z6]),(0,[z0,z1,z3,z140,z79,z6]),(0,[z0,z1,z3,z155,z5,z17]),(0,[z0,z1,z3,z67,z5,z131])],[(0,[z0,z1,z3,z1114,z5,z6]),(0,[z0,z1,z3,z1115,z5,z6]),(0,[z438,z1,z3,z33,z5,z17]),(0,[z0,z1,z3,z4,z5,z1116]),(0,[z0,z37,z3,z4,z5,z233]),(0,[z0,z1,z613,z4,z5,z29]),(0,[z0,z3,z4,z5,z1117,z6]),(0,[z0,z1,z1008,z3,z4,z29]),(0,[z0,z1,z200,z3,z223,z17]),(0,[z0,z1,z48,z3,z4,z392])],[(0,[z0,z1,z3,z1118,z5,z6]),(0,[z0,z1119,z3,z4,z5,z6]),(0,[z0,z151,z3,z4,z207,z206]),(0,[z0,z3,z4,z55,z944,z6])],[(0,[z0,z1,z3,z4,z5,z1120]),(0,[z0,z1,z3,z4,z5,z1121]),(1,[z0,z1,z4,z850,z6])],[(0,[z232,z212,z3,z4,z5,z6]),(0,[z1,z3,z4,z115,z775,z6]),(0,[z0,z1,z3,z4,z5,z326]),(0,[z1,z3,z4,z5,z1122,z6]),(0,[z0,z1,z3,z391,z5,z616])],[(0,[z0,z1123,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z317,z29]),(0,[z0,z1,z3,z4,z114,z17]),(0,[z0,z1,z3,z4,z5,z1124]),(0,[z0,z1,z1125,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1126])]],
   [[(0,[z0,z1,z3,z1127,z5,z6]),(0,[z0,z1,z178,z3,z120,z6]),(0,[z0,z1,z781,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z1128])],[(0,[z0,z1,z3,z125,z5,z342]),(0,[z0,z1,z3,z4,z5,z1129]),(0,[z0,z1,z3,z4,z138,z29])],[(0,[z0,z183,z3,z4,z317,z6]),(0,[z0,z1,z3,z4,z5,z1130]),(0,[z0,z1,z3,z4,z5,z1131]),(0,[z0,z1,z3,z318,z122,z6]),(0,[z83,z0,z3,z181,z5,z29]),(0,[z0,z559,z3,z4,z207,z6]),(0,[z0,z1,z3,z155,z5,z460])],[(0,[z0,z1,z3,z4,z5,z1132]),(0,[z0,z104,z3,z4,z5,z17]),(0,[z1056,z144,z1,z3,z4,z5])],[(0,[z0,z1,z3,z384,z5,z17]),(0,[z0,z1,z3,z4,z366,z109]),(0,[z0,z1,z3,z5,z737,z59])],[(0,[z12,z1,z3,z4,z5,z6]),(0,[z545,z1,z3,z33,z5,z6]),(0,[z0,z1,z178,z249,z3,z4]),(0,[z32,z1,z3,z726,z5,z6]),(0,[z0,z1,z3,z307,z5,z29]),(0,[z0,z1,z3,z4,z883,z45])],[(0,[z0,z906,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z29,z964]),(0,[z0,z1,z3,z5,z6,z289])],[(0,[z0,z42,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z1133])]],
   [[(0,[z211,z28,z3,z4,z5,z6]),(0,[z75,z1,z3,z4,z486,z6]),(0,[z0,z1,z3,z4,z1134,z6]),(0,[z0,z1,z3,z4,z5,z1135]),(0,[z0,z1,z3,z4,z5,z1136]),(0,[z316,z1,z3,z4,z5,z450])],[(0,[z0,z1,z1137,z3,z4,z5])],[(0,[z69,z339,z28,z3,z4,z5]),(0,[z0,z1,z3,z723,z5,z6])],[(0,[z41,z1,z3,z4,z115,z17]),(0,[z73,z1,z3,z4,z5,z268]),(0,[z1,z3,z4,z5,z6,z838]),(0,[z0,z1,z3,z127,z5,z29]),(1,[z0,z3,z4,z944,z6]),(0,[z0,z424,z3,z4,z5,z101])],[(0,[z36,z0,z3,z4,z5,z525]),(0,[z144,z1,z3,z4,z5,z29]),(0,[z0,z1,z200,z3,z509,z6]),(0,[z0,z1,z3,z384,z5,z460])],[(0,[z0,z1,z1138,z3,z5,z6]),(0,[z379,z1,z3,z318,z5,z6]),(0,[z0,z1,z3,z1139,z5,z6]),(0,[z0,z1,z3,z4,z5,z1140]),(0,[z0,z1,z3,z4,z5,z1141])],[(0,[z0,z104,z3,z4,z114,z6])],[(0,[z0,z1,z1142,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1143])]],
   [[(0,[z0,z1,z3,z4,z1144,z6]),(0,[z13,z0,z14,z4,z5,z20]),(0,[z1145,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z79,z17]),(0,[z0,z1,z8,z3,z600,z5])],[(0,[z0,z1,z3,z4,z5,z1146]),(0,[z0,z1,z3,z4,z5,z1147]),(0,[z0,z1,z221,z4,z850,z6]),(0,[z0,z1,z103,z4,z5,z29]),(0,[z0,z1,z3,z4,z1099,z17])],[(0,[z0,z1,z3,z4,z5,z1148]),(0,[z0,z1,z3,z4,z5,z1149]),(0,[z13,z260,z14,z4,z5,z6]),(0,[z1150,z1,z3,z4,z5,z6]),(0,[z1151,z1,z3,z4,z5,z6])],[(0,[z0,z104,z3,z72,z5,z6]),(0,[z0,z1152,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1153]),(0,[z0,z1,z3,z4,z5,z1154]),(0,[z0,z1,z685,z4,z107,z6])],[(0,[z0,z1155,z3,z4,z5,z6]),(0,[z0,z1156,z3,z4,z5,z6]),(0,[z1157,z1,z3,z4,z5,z6]),(0,[z1158,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1159,z5,z6]),(0,[z0,z1,z3,z1160,z5,z6]),(0,[z0,z1,z3,z4,z5,z1161]),(0,[z0,z1,z3,z155,z5,z29])],[(0,[z438,z1,z3,z33,z5,z29]),(0,[z0,z1,z282,z4,z5,z17]),(0,[z379,z1,z3,z4,z122,z6]),(0,[z1162,z1,z3,z4,z5,z6]),(0,[z0,z1,z200,z3,z223,z29]),(0,[z0,z1,z200,z3,z683,z6])],[(0,[z0,z1,z3,z4,z5,z17]),(0,[z0,z1,z178,z3,z374,z4]),(0,[z0,z1,z238,z140,z5,z6]),(0,[z96,z151,z3,z4,z5,z6]),(0,[z0,z1,z1059,z3,z5,z29])]],
   [[(0,[z69,z906,z3,z4,z5,z6]),(0,[z906,z28,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1163]),(0,[z0,z1,z3,z251,z5,z17]),(0,[z0,z1,z3,z503,z5,z17]),(0,[z260,z1,z3,z4,z5,z17])],[(0,[z232,z27,z3,z4,z5,z17]),(0,[z65,z1,z186,z4,z5,z17]),(0,[z0,z1,z46,z148,z5,z6])],[(0,[z0,z1,z3,z4,z114,z29])],[(0,[z65,z104,z3,z4,z5,z6]),(0,[z748,z0,z1,z3,z4,z5])],[(0,[z28,z3,z4,z403,z5,z6]),(0,[z1,z843,z39,z4,z5,z6]),(0,[z0,z1,z1164,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z1165]),(0,[z0,z1066,z3,z4,z5,z29]),(0,[z0,z1119,z3,z4,z5,z17])],[(0,[z0,z1,z3,z4,z5,z1166]),(0,[z0,z1,z3,z4,z1167,z6]),(0,[z0,z183,z3,z4,z114,z6]),(0,[z0,z1,z3,z1168,z5,z6]),(0,[z0,z1,z3,z4,z5,z1169])],[(0,[z0,z104,z3,z4,z5,z29]),(0,[z0,z1170,z3,z4,z5,z6]),(0,[z0,z1,z227,z3,z5,z44])],[(0,[z0,z1,z3,z1171,z4,z5]),(0,[z0,z1,z3,z4,z944,z6]),(0,[z0,z1,z527,z4,z68,z6]),(0,[z0,z1,z3,z4,z5,z460]),(0,[z0,z1,z3,z384,z5,z29])]],
   [[(0,[z0,z1,z1172,z4,z5,z6])],[(0,[z0,z1,z3,z4,z6,z1173]),(0,[z0,z1,z3,z67,z5,z22])],[(0,[z506,z1,z39,z4,z5,z6]),(0,[z64,z1,z3,z4,z115,z6]),(0,[z0,z1,z3,z4,z114,z6]),(0,[z38,z1,z39,z4,z5,z311]),(0,[z0,z1,z3,z4,z5,z1174]),(0,[z0,z1175,z3,z4,z5,z6]),(0,[z1176,z1,z3,z4,z5,z6]),(0,[z0,z1,z1080,z3,z5,z29])],[(0,[z41,z99,z3,z4,z115,z6]),(0,[z0,z1,z4,z5,z703,z29]),(0,[z1177,z1,z3,z4,z5,z6]),(0,[z0,z1,z46,z723,z5,z6]),(0,[z1178,z1,z3,z4,z5,z6]),(0,[z0,z1,z278,z3,z4,z294])],[(0,[z1179,z0,z3,z4,z5,z6]),(0,[z66,z1,z3,z307,z5,z70])],[(0,[z12,z1,z3,z4,z5,z17]),(0,[z0,z1,z3,z4,z5,z217])],[(0,[z0,z1,z3,z4,z5,z1180]),(0,[z0,z1,z479,z3,z33,z5]),(0,[z41,z1,z3,z4,z115,z29]),(0,[z0,z1,z258,z4,z5,z29]),(0,[z0,z1,z1181,z4,z5,z6]),(0,[z0,z1,z23,z4,z68,z74]),(0,[z197,z1,z3,z4,z5,z309])],[(0,[z0,z1,z3,z72,z5,z6]),(0,[z66,z1,z3,z678,z4,z5]),(0,[z0,z1,z3,z4,z5,z1182]),(0,[z934,z0,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z72,z5,z311]),(0,[z0,z1,z3,z1183,z5,z6]),(0,[z0,z1,z3,z127,z5,z213]),(0,[z0,z1,z3,z318,z5,z20]),(0,[z1184,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1185]),(0,[z0,z1,z3,z4,z17,z803]),(0,[z0,z1,z3,z4,z793,z6])],[(0,[z0,z1,z3,z4,z1186,z6]),(0,[z36,z0,z3,z4,z5,z722]),(0,[z0,z1,z1187,z4,z5,z6])],[(0,[z0,z3,z819,z181,z5,z6])],[(0,[z0,z1,z3,z4,z1188,z6]),(0,[z0,z1,z3,z4,z5,z1189]),(0,[z1190,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z79,z29]),(0,[z0,z1,z3,z4,z5,z1191])],[(0,[z0,z3,z744,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1192]),(0,[z11,z0,z3,z4,z944,z6])],[(0,[z0,z1,z3,z4,z5,z1193]),(0,[z0,z1,z3,z4,z1194,z6]),(0,[z411,z1,z3,z9,z5,z6]),(0,[z0,z1,z4,z107,z850,z6])],[(0,[z501,z27,z3,z4,z5,z6]),(0,[z75,z1,z3,z251,z34,z6]),(0,[z0,z175,z3,z4,z5,z101]),(0,[z0,z1,z46,z148,z5,z635]),(0,[z0,z1,z585,z4,z5,z29])],[(0,[z0,z99,z3,z4,z5,z6]),(0,[z0,z1,z1195,z3,z4,z5]),(0,[z0,z1,z584,z4,z5,z29]),(0,[z1196,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z374,z5,z257])],[(0,[z0,z1,z3,z1197,z5,z6]),(0,[z38,z1,z39,z4,z317,z6]),(0,[z0,z1,z3,z4,z5,z1198]),(0,[z0,z524,z3,z4,z5,z101]),(0,[z0,z1,z103,z4,z68,z6])],[(0,[z0,z1,z3,z4,z5,z29]),(0,[z32,z1,z3,z9,z5,z17]),(0,[z75,z99,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1199])],[(0,[z0,z1,z3,z4,z5,z1200]),(0,[z0,z1,z3,z251,z5,z29]),(0,[z0,z1,z3,z503,z5,z29]),(0,[z260,z1,z3,z4,z5,z29]),(0,[z0,z844,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z793,z6]),(1,[z0,z1,z3,z4,z883])],[(0,[z65,z1,z186,z4,z5,z29]),(0,[z0,z1,z3,z4,z1201,z6])],[(0,[z0,z183,z3,z4,z5,z6]),(0,[z0,z1,z3,z170,z5,z6]),(0,[z0,z1,z3,z4,z199,z6]),(1,[z0,z744,z4,z5,z6]),(0,[z0,z1,z3,z1202,z5,z6])],[(0,[z0,z339,z3,z4,z5,z101]),(0,[z0,z1,z1203,z3,z4,z5]),(0,[z0,z1,z3,z125,z5,z311]),(0,[z0,z1204,z3,z4,z5,z6]),(0,[z438,z1,z178,z3,z33,z6]),(0,[z0,z1,z3,z5,z6,z1205]),(0,[z73,z1,z88,z3,z4,z5]),(0,[z260,z1,z3,z4,z199,z6]),(0,[z0,z1,z3,z4,z5,z135]),(0,[z0,z1,z196,z3,z4,z45]),(0,[z0,z1,z47,z140,z5,z102]),(0,[z0,z1,z3,z5,z257,z523]),(0,[z0,z1,z8,z3,z407,z5])],[(0,[z0,z339,z100,z3,z4,z5]),(0,[z0,z1,z3,z72,z317,z6]),(0,[z0,z1,z301,z4,z5,z29]),(0,[z784,z0,z3,z4,z5,z6]),(0,[z0,z1,z141,z4,z5,z29])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 533).take 534) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1067).take 152) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1219)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [533, 534, 152] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 120).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 246).take 10).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [120, 126, 10] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_38927

theorem PEqualNP.Outside.L_meta_38927 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38927.solve