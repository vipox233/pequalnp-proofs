import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38835

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
  Nat.testBit (4276808928 * 2 ^ 32 + 4272611488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x001053c42108b0ac#64 ++ 0x20020a7884211615#64 ++ 0x9831f7c4611ff1ff#64 ++ 0xd3063ef88c23fe3f#64 : BitVec 256),
   (0x0846c0dd91659661#64 ++ 0x4108d81bb22cb2cc#64 ++ 0xe8cec9ff91e59e67#64 ++ 0xbd19d93ff23cb3cc#64 : BitVec 256),
   (0x030b0c02d6060b51#64 ++ 0x806161805ac0c16a#64 ++ 0xb70f0e07fe061fff#64 ++ 0x76e1e1c0ffc0c3ff#64 : BitVec 256),
   (0x15b00f680bb81d86#64 ++ 0x02b601ed017703b0#64 ++ 0xfff00ff81ff81f86#64 ++ 0xfffe01ff03ff03f0#64 : BitVec 256),
   (0x06efa0001cd74000#64 ++ 0x00ddf400039ae800#64 ++ 0xdffff0001fffe005#64 ++ 0xfbfffe0003fffc00#64 : BitVec 256),
   (0x27fdffb760000000#64 ++ 0x04ffbff6ec000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [12, 5]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x9831f7c4611ff1ff 0xd3063ef88c23fe3f

def z1 : W := mkw 0x01100f4003081984 0x002201e800610330 0xbf300fc01f181f86 0xf7e601f803e303f0

def z2 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xb70f0e07fe061fff 0x76e1e1c0ffc0c3ff

def z3 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff0001fffe005 0xfbfffe0003fffc00

def z4 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cec9ff91e59e67 0xbd19d93ff23cb3cc

def z5 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff00ff81ff81f86 0xfffe01ff03ff03f0

def z6 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x08020048916db6ed 0x61004009122db6dd 0x1800000011fffffc 0x03000000023fffff

def z8 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x270f0807fe060e79 0x24e1e100ffc0c1cf

def z9 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x0800000011e59e64 0x01000000023cb3cc

def z10 : W := mkw 0x2ffffffff1659661 0x45fffffffe2cb2cc 0xeffffffff1e59e67 0xfdfffffffe3cb3cc

def z11 : W := mkw 0x03090c0246020910 0x8061218048c04122 0xb70f0e07ee02019b 0x76e1e1c0fdc04033

def z12 : W := mkw 0x31105fff63281d86 0x06220bffec6503b0 0x20000fffe0001f82 0x040001fffc0003f0

def z13 : W := mkw 0x15a00c680bb01d02 0x02b4018d017603a0 0xefc009f81fe01e06 0xbdf8013f03fc03c0

def z14 : W := mkw 0x001013002008208c 0x2002026004010411 0x10313600601a6198 0x420626c00c034c33

def z15 : W := mkw 0x27fdffb76008208c 0x24ffbff6ec010411 0xf7ffffffe01a619b 0xfefffffffc034c33

def z16 : W := mkw 0x04e4a00008d14000 0x009c9400011a2800 0x48f0f00001f9e000 0x891e1e00003f3c00

def z17 : W := mkw 0x0eefe0dd9df7d661 0x41ddfc1bb3befacc 0xfffff9ff9ffffe67 0xffffff3ff3ffffcc

def z18 : W := mkw 0x0844c09500418020 0x41089812a0083004 0x0000c00000018000 0x0000180000003000

def z19 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x0831f1c4611fe079 0x81063e388c23fc0f

def z20 : W := mkw 0x000200001cd74000 0x00004000039ae800 0x180000001fffe004 0x0300000003fffc00

def z21 : W := mkw 0x15b05fe42b98b9ae 0x22b60bfc85731735 0x9f31f7c46f1ff1ff 0xd3e63ef88de3fe3f

def z22 : W := mkw 0x2ffffffffdf7d661 0x45ffffffffbefacc 0xfffffffffffffe67 0xffffffffffffffcc

def z23 : W := mkw 0x01105fc6e308bbfd 0xa0220bf8dc61177f 0x20000fc7e0001ffa 0x040001f8fc0003ff

def z24 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x000007c4600011fa 0x000000f88c00023f

def z25 : W := mkw 0x06fff3c43ddff0ac 0x20dffe7887bbfe15 0xdffff7c47ffff1ff 0xfbfffef88ffffe3f

def z26 : W := mkw 0x15f4af680bf95d86 0x02be95ed017f2bb0 0xfff0fff81ff9ff86 0xfffe1fff03ff3ff0

def z27 : W := mkw 0x001053842008a0ac 0x20020a7084011415 0x1031f604601fe1f9 0x42063ec08c03fc3f

def z28 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x270e08039e000e00 0x24e1c10073c001c0

def z29 : W := mkw 0x07efac02ded74b51 0x80fdf5805bdae96a 0xfffffe07ffffffff 0xffffffc0ffffffff

def z30 : W := mkw 0x0a4fc0dd95679661 0x4149f81bb2acf2cc 0xffcfc9ff9fe79e67 0xfff9f93ff3fcf3cc

def z31 : W := mkw 0x03195fc6670ab9bc 0xa0632bf8cce15737 0x9f31f7c46f1ff1ff 0xd3e63ef88de3fe3f

def z32 : W := mkw 0x020b0002d4060251 0x804160005a80c04a 0x000e000380000000 0x0001c00070000000

def z33 : W := mkw 0x025ff3c4354ff0ac 0x204bfe7886a9fe15 0x983ff7c4611ff1ff 0xd307fef88c23fe3f

def z34 : W := mkw 0x01020c0092040b41 0x0020418012408168 0xb70e0e079e041fe7 0x76e1c1c0f3c083fc

def z35 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xe0cec9ff80000003 0xbc19d93ff0000000

def z36 : W := mkw 0x0846801990650641 0x4108d003320ca0c8 0x60ce083b90e00e00 0x2c19c107721c01c0

def z37 : W := mkw 0x04e6a00018d54000 0x009cd400031aa800 0xc8fef00011fde005 0xb91fde00023fbc00

def z38 : W := mkw 0x034f8c02d6470b51 0x8069f1805ac8e16a 0xffcfce07ffe79fff 0xfff9f9c0fffcf3ff

def z39 : W := mkw 0x11000c2802200d02 0x02200185004401a0 0x2000083800000e00 0x04000107000001c0

def z40 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x900107c4600611ff 0x520020f88c00c23f

def z41 : W := mkw 0x01105fc42308b9ac 0x20220bf884611735 0xbf31ffc47f1fffff 0xf7e63ff88fe3ffff

def z42 : W := mkw 0x15b00f200a980986 0x02b601e401530130 0xf7f00ff80e180182 0xfefe01ff01c30030

def z43 : W := mkw 0x03090c0240000000 0x0061218048000000 0x270e080380000000 0x24e1c10070000000

def z44 : W := mkw 0x0846c09590458261 0x4108d812b208b04c 0x000ec00780058061 0x0001d800f000b00c

def z45 : W := mkw 0x15b05fec2bb8bdae 0x22b60bfd857717b5 0xfff1fffc7fffffff 0xfffe3fff8fffffff

def z46 : W := mkw 0x225df39760000000 0x044bbe72ec000000 0x803ff7c7e0000003 0xd007fef8fc000000

def z47 : W := mkw 0x04a0000008900000 0x0094000001120000 0xdff000001ff80004 0xfbfe000003ff0000

def z48 : W := mkw 0x020b000014060000 0x004160000280c000 0x9f3ff0001f1fe005 0xf3e7fe0003e3fc00

def z49 : W := mkw 0x080040dd81209661 0x4100081bb02412cc 0x200009ff80001e62 0x0400013ff00003cc

def z50 : W := mkw 0x0856d3ddb16db6ed 0x610ada7bb62db6dd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z51 : W := mkw 0x0856c3dd916d96e5 0x410ad87bb22db2dc 0xf8fecfff91fd9fe7 0xff1fd9fff23fb3fc

def z52 : W := mkw 0x03090c0246020910 0x8061218048c04122 0x170106006e020198 0x42e020c00dc04033

def z53 : W := mkw 0x0844c0dd01619420 0x4108981ba02c3284 0x48c0c1f801e18000 0x8918183f003c3000

def z54 : W := mkw 0x100000480bb81d86 0x02000009017703b0 0x180000001ff81f84 0x0300000003ff03f0

def z55 : W := mkw 0x0010030000000000 0x0002006000000000 0x803007c000000002 0xd00600f800000000

def z56 : W := mkw 0x09004cdfc3209f71 0xc120099bf86413ee 0x20000fffe0001ffa 0x040001fffc0003ff

def z57 : W := mkw 0x03090c0240000000 0x0061218048000000 0xa70f0e07e0000003 0x74e1e1c0fc000000

def z58 : W := mkw 0x21105fb7e2000b51 0x84220bf6fc40016a 0x20000fffe0001ffa 0x040001fffc0003ff

def z59 : W := mkw 0x15b00f200a980986 0x02b601e401530130 0x173006000e180180 0x42e600c001c30030

def z60 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x47ce00001ee00000 0x28f9c00003dc0000

def z61 : W := mkw 0x024fa00014474000 0x0049f4000288e800 0x000e000000000000 0x0001c00000000000

def z62 : W := mkw 0x031b0f42d70e1bd5 0x806361e85ae1c37a 0xbf3f0fc7ff1e1fff 0xf7e7e1f8ffe3c3ff

def z63 : W := mkw 0x15a00c280ab00d02 0x02b40185015601a0 0x67c008381ee00e00 0x2cf8010703dc01c0

def z64 : W := mkw 0x224df09760000000 0x0449be12ec000000 0x000ff007e0000001 0x0001fe00fc000000

def z65 : W := mkw 0x000000400108b0ac 0x2000000800211615 0x18000000011ff1fc 0x030000000023fe3f

def z66 : W := mkw 0x0010538420000000 0x00020a7084000000 0x8031f7c460000003 0xd0063ef88c000000

def z67 : W := mkw 0x14b053ec29b8b4ae 0x22960a7d85371695 0xd8f1f7fc61fff1ff 0xdb1e3eff8c3ffe3f

def z68 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xf7ffffffe00611ff 0xfefffffffc00c23f

def z69 : W := mkw 0x020b5086f406a279 0xa0416a10de80d44f 0x000ff007e007e079 0x0001fe00fc00fc0f

def z70 : W := mkw 0x27edac3340000000 0x04fdb58668000000 0xe7cf0e3fe0000003 0x7cf9e1c7fc000000

def z71 : W := mkw 0x04b0034009981084 0x0096006801330210 0xdff007c01ff81186 0xfbfe00f803ff0230

def z72 : W := mkw 0x01000c0002000900 0x0020018000400120 0x170006000e000180 0x42e000c001c00030

def z73 : W := mkw 0x024fa00014474000 0x0049f4000288e800 0x000ff0000007e001 0x0001fe000000fc00

def z74 : W := mkw 0x11100f6803281d86 0x022201ed006503b0 0x20000ff800001f82 0x040001ff000003f0

def z75 : W := mkw 0x031b5fc6f70ebbfd 0xa0636bf8dee1d77f 0xbf3fffc7ff1fffff 0xf7e7fff8ffe3ffff

def z76 : W := mkw 0x06efa0009ed74b51 0x80ddf40013dae96a 0xdffff0001ffffffd 0xfbfffe0003ffffff

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0x90010604600611ff 0x520020c08c00c23f

def z78 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff6047ffff1ff 0xfbfffec08ffffe3f

def z79 : W := mkw 0x224da01340000000 0x0449b40268000000 0x000e000380000000 0x0001c00070000000

def z80 : W := mkw 0x0044c0d501009020 0x0008981aa0201204 0xe8cec9ff81059067 0xbd19d93ff020b20c

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0x9831f000011fe005 0xd3063e000023fc00

def z82 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8fff9ff91fffe67 0xff1fff3ff23fffcc

def z83 : W := mkw 0x0b4f8c1bd6670f51 0xc169f1837acce1ea 0xf7cf0e3ffee61fff 0x7ef9e1c7ffdcc3ff

def z84 : W := mkw 0x27fdffb766020910 0x84ffbff6ecc04122 0xf7ffffffee02019b 0xfefffffffdc04033

def z85 : W := mkw 0x0854d3dd2169b4ac 0x610a9a7ba42d3695 0xd8f1f7fc61fff1ff 0xdb1e3eff8c3ffe3f

def z86 : W := mkw 0x080200489df7d661 0x4100400913befacc 0x180000001ffffe64 0x0300000003ffffcc

def z87 : W := mkw 0x000000400108b0ac 0x2000000800211615 0x9831f000011ff1fd 0xd3063e000023fe3f

def z88 : W := mkw 0x0000004801201400 0x0000000900240280 0xe8c009f811e01e06 0xbd18013f023c03c0

def z89 : W := mkw 0x0df6cffd91659661 0x41bed9ffb22cb2cc 0xeffecfff91e59e67 0xfdffd9fff23cb3cc

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800c00001058005 0x910018000020b000

def z91 : W := mkw 0x15b01f682bb83d8e 0x22b603ed057707b1 0xfff13ff87ffa7f9e 0xfffe27ff0fff4ff3

def z92 : W := mkw 0x000050842000a028 0x20000a1084001405 0x0001f0046007e079 0x00003e008c00fc0f

def z93 : W := mkw 0x0846c09d90650641 0x4108d813b20ca0c8 0xe0cec9ff90e00e03 0xbc19d93ff21c01c0

def z94 : W := mkw 0x0046c09590040241 0x0008d812b2008048 0xe0cec9ff90041e67 0xbc19d93ff20083cc

def z95 : W := mkw 0x27fdaf3340000000 0x04ffb5e668000000 0xe7fe0ffb80000002 0xfcffc1ff70000000

def z96 : W := mkw 0x17b90f6a4fba1d96 0x82f721ed49f743b2 0xfff10ff87ffa1f9e 0xfffe21ff0fff43f3

def z97 : W := mkw 0x27efac335cd74000 0x04fdf5866b9ae800 0x67ce083b9ee00000 0x2cf9c10773dc0000

def z98 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67ce0fffe0000002 0x2cf9c1fffc000000

def z99 : W := mkw 0x031b5fc6f70ebbfd 0xa0636bf8dee1d77f 0xb70f0fc7fe061fff 0x76e1e1f8ffc0c3ff

def z100 : W := mkw 0x0002000014060000 0x000040000280c000 0x100000001e060004 0x0200000003c0c000

def z101 : W := mkw 0x0002000090040241 0x0000400012008048 0x0000000010041e64 0x00000000020083cc

def z102 : W := mkw 0x034fcc97d6060b51 0x8069f992fac0c16a 0xf7cfcffffe061fff 0xfef9f9ffffc0c3ff

def z103 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x270e0e07fe001ffa 0x24e1c1c0ffc003ff

def z104 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x60ce09ff90e01e62 0x2c19c13ff21c03cc

def z105 : W := mkw 0x14b0036809b81486 0x0296006d01370290 0x48f001f801f80000 0x891e003f003f0000

def z106 : W := mkw 0x0002004891241641 0x00004009122482c8 0xe8ce09ff91e41e67 0xbd19c13ff23c83cc

def z107 : W := mkw 0x17bb0f6adfbe1fd7 0x82f761ed5bf7c3fa 0xffff0ffffffe1fff 0xffffe1ffffffc3ff

def z108 : W := mkw 0x0010538420000000 0x00020a7084000000 0x9831f7c4611fe007 0xd3063ef88c23fc00

def z109 : W := mkw 0x0002000090040241 0x0000400012008048 0xa00e080790041e67 0x3401c100f20083cc

def z110 : W := mkw 0x06eda00000000000 0x00ddb40000000000 0xc7fff00000000001 0xf8fffe0000000000

def z111 : W := mkw 0x27ffffb77cd74000 0x04fffff6ef9ae800 0xffffffffffffe007 0xfffffffffffffc00

def z112 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff10ffc7ffe1fff 0xfffe21ff8fffc3ff

def z113 : W := mkw 0x11100f6803281d86 0x022201ed006503b0 0xb8300ff801181f86 0xd70601ff002303f0

def z114 : W := mkw 0x06eda0000cd34000 0x00ddb400019a6800 0x5ff1f0000ffbe000 0xcbfe3e0001ff7c00

def z115 : W := mkw 0x11100f6ac3281fd7 0x822201ed586503fa 0x20000fffe0001ffa 0x040001fffc0003ff

def z116 : W := mkw 0x0046c0c411459020 0x0008d8188228b204 0xc8cec1c411e59067 0xb919d838823cb20c

def z117 : W := mkw 0x020b0002d4060251 0x804160005a80c04a 0x000f0007e0060079 0x0001e000fc00c00f

def z118 : W := mkw 0x24f4f3f52108b0ac 0x249e9e7ea4211615 0xd8f1f7fc611ff1ff 0xdb1e3eff8c23fe3f

def z119 : W := mkw 0x0044c09500000000 0x00089812a0000000 0x40c0c1f800000000 0x8818183f00000000

def z120 : W := mkw 0x0002000096060b51 0x8000400012c0c16a 0x100000001e061ffc 0x0200000003c0c3ff

def z121 : W := mkw 0x24f4f3b520000000 0x049e9e76a4000000 0x40f0f1f800000000 0x881e1e3f00000000

def z122 : W := mkw 0x1de68c399af50f43 0x43bcd187335ea1e8 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z123 : W := mkw 0x000040c401009020 0x0000081880201204 0x8800c1c401059067 0x910018388020b20c

def z124 : W := mkw 0x11100f6803281d86 0x022201ed006503b0 0xb7000ff81e001f86 0x76e001ff03c003f0

def z125 : W := mkw 0x37b93f6a6bb81d86 0x06f727ed4d7703b0 0xfff13ff87ff81f86 0xfffe27ff0fff03f0

def z126 : W := mkw 0x01000c02c2000b51 0x802001805840016a 0xb0010e07e0061fff 0x560021c0fc00c3ff

def z127 : W := mkw 0x27fdffb76000a028 0x24ffbff6ec001405 0xe7ffffffe007e07b 0xfcfffffffc00fc0f

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001e000004 0x72e0000003c00000

def z129 : W := mkw 0x27fdffb7e2000b51 0x84ffbff6fc40016a 0xe7ffffffe0001ffb 0xfcfffffffc0003ff

def z130 : W := mkw 0x01000c02c2000b51 0x802001805840016a 0x20000e07e0001ffa 0x040001c0fc0003ff

def z131 : W := mkw 0x37ffffff7fff5d86 0x06ffffffefffebb0 0xffffffffffffff87 0xfffffffffffffff0

def z132 : W := mkw 0x21105fb760000000 0x04220bf6ec000000 0x20000fffe0000002 0x040001fffc000000

def z133 : W := mkw 0x06efe0951cd74000 0x00ddfc12a39ae800 0xfffff9ff9fffe007 0xffffff3ff3fffc00

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x8031f00000000001 0xd0063e0000000000

def z135 : W := mkw 0x27fdfff76108b0ac 0x24ffbffeec211615 0xe7ffffffe00011fb 0xfcfffffffc00023f

def z136 : W := mkw 0x0846801190450241 0x4108d0023208a048 0x000e000380000000 0x0001c00070000000

def z137 : W := mkw 0x0000004001081084 0x0000000800210210 0x1800000001181184 0x0300000000230230

def z138 : W := mkw 0x06a920000c924000 0x00d5240001924800 0x173130000e1a6000 0x42e6260001c34c00

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000011fe004 0x030000000023fc00

def z140 : W := mkw 0x06ede09500000000 0x00ddbc12a0000000 0xe7fff9ff80000003 0xfcffff3ff0000000

def z141 : W := mkw 0x2209300260000000 0x044126004c000000 0x0001300060000000 0x000026000c000000

def z142 : W := mkw 0x080040dd81209661 0x4100081bb02412cc 0xa800c9ff81059e67 0x9500193ff020b3cc

def z143 : W := mkw 0x27edac3340000000 0x04fdb58668000000 0x67ce083b80000000 0x2cf9c10770000000

def z144 : W := mkw 0x04a0000008900000 0x0094000001120000 0x48f0000001f80000 0x891e0000003f0000

def z145 : W := mkw 0x2ffdffff61619420 0x45ffbfffec2c3284 0xefffffffe1e18003 0xfdfffffffc3c3000

def z146 : W := mkw 0x01000c0002000900 0x0020018000400120 0xb7000e001e001f86 0x76e001c003c003f0

def z147 : W := mkw 0x034fac02d6474b51 0x8069f5805ac8e96a 0xb70ffe07fe07ffff 0x76e1ffc0ffc0ffff

def z148 : W := mkw 0x0000004801201400 0x0000000900240280 0x0800000011e01e04 0x01000000023c03c0

def z149 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xb70f08039e060e05 0x76e1e10073c0c1c0

def z150 : W := mkw 0x1956cffd936d9fe7 0x432ad9ffb26db3fc 0xe8cecfff91e59fe7 0xbd19d9fff23cb3fc

def z151 : W := mkw 0x101053cc2bb8bdae 0x22020a79857717b5 0x9831f7c47fffffff 0xd3063ef88fffffff

def z152 : W := mkw 0x27b93f226008208c 0x24f727e44c010411 0x17313600601a6198 0x42e626c00c034c33

def z153 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xc7fff0001ee00001 0xf8fffe0003dc0000

def z154 : W := mkw 0x0844801900610400 0x41089003200c2080 0x40c0003800e00000 0x08180007001c0000

def z155 : W := mkw 0x0846805991651641 0x4108d00b322ca2c8 0xe8ce09fb91e01e06 0xbd19c13f723c03c0

def z156 : W := mkw 0x03090c0240000000 0x0061218048000000 0x0701060060000000 0x40e020c00c000000

def z157 : W := mkw 0x0046800010450000 0x0008d0000208a000 0xc8cec00011e58005 0xb919d800023cb000

def z158 : W := mkw 0x06a9200000000000 0x00d5240000000000 0x0731300000000000 0x40e6260000000000

def z159 : W := mkw 0x3ffffffffbfd9fe7 0x47ffffffff7fb3fc 0xfffffffffffd9fe7 0xffffffffffffb3fc

def z160 : W := mkw 0x0054d3d52108b0ac 0x200a9a7aa4211615 0xf8ffffffe11ff1ff 0xff1ffffffc23fe3f

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z162 : W := mkw 0x27fdffb768d14000 0x04ffbff6ed1a2800 0xefffffffe1f9e003 0xfdfffffffc3f3c00

def z163 : W := mkw 0x0b4fcc97d6478b71 0xc169f992fac8f16e 0xb70fce07fe079fff 0x76e1f9c0ffc0f3ff

def z164 : W := mkw 0x27b93f2260000000 0x04f727e44c000000 0x0731360060000000 0x40e626c00c000000

def z165 : W := mkw 0x000040c40108b0ac 0x2000081880211615 0x9800c1c4011ff1ff 0x930018388023fe3f

def z166 : W := mkw 0x0000408400008020 0x0000081080001004 0x0000c00400058061 0x000018008000b00c

def z167 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x1831f7c0611be198 0xc3063ef80c237c33

def z168 : W := mkw 0x37fdffff6bb81d86 0x06ffbfffed7703b0 0xfffffffffff81f87 0xffffffffffff03f0

def z169 : W := mkw 0x2cf4f3fd21619420 0x459e9e7fa42c3284 0x48f0f1f801e18000 0x891e1e3f003c3000

def z170 : W := mkw 0x081253ccb16db6ed 0x61024a79962db6dd 0x9831f7c471ffffff 0xd3063ef88e3fffff

def z171 : W := mkw 0x0010034001081084 0x0002006800210210 0x983107c4611e11ff 0xd30620f88c23c23f

def z172 : W := mkw 0x26fff3b53cd74000 0x04dffe76a79ae800 0xdffff1f81fffe005 0xfbfffe3f03fffc00

def z173 : W := mkw 0x05b00f6801201400 0x00b601ed00240280 0xeff00ff811e01e06 0xfdfe01ff023c03c0

def z174 : W := mkw 0x14b0036809b81486 0x0296006d01370290 0xe8f009f811f81e06 0xbd1e013f023f03c0

def z175 : W := mkw 0x19104ffd83289fe7 0x432209ffb06513fc 0x20000fff80001fe2 0x040001fff00003fc

def z176 : W := mkw 0x001053c421009020 0x00020a7884201204 0x8831f7c461059067 0xd1063ef88c20b20c

def z177 : W := mkw 0x06efe0c41dd7d020 0x00ddfc1883bafa04 0xdffff1c41ffff067 0xfbfffe3883fffe0c

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00e080780000003 0x3401c100f0000000

def z179 : W := mkw 0x024f800014470000 0x0049f0000288e000 0xdfcfc0001fe78005 0xfbf9f80003fcf000

def z180 : W := mkw 0x04a0004809b01400 0x0094000901360280 0xfff009f81ff81e06 0xfffe013f03ff03c0

def z181 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8cfcffff1e79fff 0xff19f9fffe3cf3ff

def z182 : W := mkw 0x15b05fec2bb8bdae 0x22b60bfd857717b5 0xfff0fff81ff9ff86 0xfffe1fff03ff3ff0

def z183 : W := mkw 0x0946ccdd93659f61 0x4128d99bb26cb3ec 0xffcecfff9fe59fe7 0xfff9d9fff3fcb3fc

def z184 : W := mkw 0x27ffffb7f6060b51 0x84fffff6fec0c16a 0xf7fffffffe061fff 0xfeffffffffc0c3ff

def z185 : W := mkw 0x024fa00014474000 0x0049f4000288e800 0x970ff0001e07e005 0x72e1fe0003c0fc00

def z186 : W := mkw 0x030b0c0016060900 0x0061618002c0c120 0xb70f0e001e061f87 0x76e1e1c003c0c3f0

def z187 : W := mkw 0x0046804811651400 0x0008d009022ca280 0xe8cec9f811e59e07 0xbd19d93f023cb3c0

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x10313000001a6000 0x4206260000034c00

def z189 : W := mkw 0x0846d0ddb165b669 0x6108da1bb62cb6cd 0xe8cff9fff1e7fe7f 0xbd19ff3ffe3cffcf

def z190 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x47f1f7f860000000 0xc8fe3eff0c000000

def z191 : W := mkw 0x0b4fccdfd7679f71 0xc169f99bfaecf3ee 0xffcfcfffffe79fff 0xfff9f9fffffcf3ff

def z192 : W := mkw 0x06efa002dcd74251 0x80ddf4005b9ae84a 0xdffff007ffffe07d 0xfbfffe00fffffc0f

def z193 : W := mkw 0x0056d3c4314db0ac 0x200ada788629b615 0xd8fff7c471fff1ff 0xfb1ffef88e3ffe3f

def z194 : W := mkw 0x0856d3ddb16db6ed 0x610ada7bb62db6dd 0xe8fef9ff91fdfe67 0xbd1fdf3ff23fbfcc

def z195 : W := mkw 0x27edfcb760000000 0x04fdbf96ec000000 0x67cff83fe0000001 0x2cf9ff07fc000000

def z196 : W := mkw 0x0846c0dd9df7d661 0x4108d81bb3befacc 0xf8cec9ff9ffffe67 0xbf19d93ff3ffffcc

def z197 : W := mkw 0x024fa00014474000 0x0049f4000288e800 0xc8cff00011e7e005 0xb919fe00023cfc00

def z198 : W := mkw 0x01020c0096060b51 0x8020418012c0c16a 0xb7000e001e061ffe 0x76e001c003c0c3ff

def z199 : W := mkw 0x17b90f224e9a0996 0x82f721e449d34132 0x173106006e1a0198 0x42e620c00dc34033

def z200 : W := mkw 0x0002000010450000 0x000040000208a000 0x0800000011e58004 0x01000000023cb000

def z201 : W := mkw 0x07ffaf201cd74000 0x00fff5e4039ae800 0xfffffff81fffe007 0xffffffff03fffc00

def z202 : W := mkw 0x17ffaf681fff5d86 0x02fff5ed03ffebb0 0xfffe0ff81ff81f86 0xffffc1ff03ff03f0

def z203 : W := mkw 0x031b5f86f6060b51 0x80636bf0dec0c16a 0xb73fffc7fe061fff 0xf6e7fff8ffc0c3ff

def z204 : W := mkw 0x06eff0843cd7e028 0x20ddfe10879afc05 0xdffff0047fffe07d 0xfbfffe008ffffc0f

def z205 : W := mkw 0x0002000014474000 0x000040000288e800 0x000000000007e000 0x000000000000fc00

def z206 : W := mkw 0x07efac02ded74b51 0x80fdf5805bdae96a 0xfffff8039fffee05 0xffffff0073fffdc0

def z207 : W := mkw 0x0010030000080084 0x0002006000010010 0x1030060000180180 0x420600c000030030

def z208 : W := mkw 0x081053dda128b6ed 0x61020a7bb42516dd 0xb831ffffe11fffff 0xd7063ffffc23ffff

def z209 : W := mkw 0x080240dd91659661 0x4100481bb22cb2cc 0x280009ff91e59e66 0x0500013ff23cb3cc

def z210 : W := mkw 0x2fefac3bd0650641 0x45fdf5877a0ca0c8 0x67ce083b90e00e00 0x2cf9c107721c01c0

def z211 : W := mkw 0x0000408400000000 0x0000081080000000 0x8000c1c400000003 0x9000183880000000

def z212 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x0830f7c46119f1fa 0x81061ef88c233e3f

def z213 : W := mkw 0x06efa0009cd74241 0x00ddf400139ae848 0xfffff8079ffffe67 0xffffff00f3ffffcc

def z214 : W := mkw 0x001013002008208c 0x2002026004010411 0x90313604601e71ff 0x520626c08c03ce3f

def z215 : W := mkw 0x030b0c4ad7261f51 0x806161895ae4c3ea 0xffcf0fffffe61fff 0xfff9e1fffffcc3ff

def z216 : W := mkw 0x1db20f689bfd9fe7 0x43b641ed137fb3fc 0xfff00ff81ffd9fe6 0xfffe01ff03ffb3fc

def z217 : W := mkw 0x27edecb740000000 0x04fdbd96e8000000 0xe7cec9ff80000003 0xbcf9d93ff0000000

def z218 : W := mkw 0x27fdffff61201400 0x04ffbfffec240280 0xeffffffff1e01e07 0xfdfffffffe3c03c0

def z219 : W := mkw 0x25f4ffb760000000 0x04be9ff6ec000000 0x60f0ffffe0000002 0x8c1e1ffffc000000

def z220 : W := mkw 0x26fdf3b520000000 0x04dfbe76a4000000 0xc7fff1f800000001 0xf8fffe3f00000000

def z221 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x1f3006001ff81f84 0x43e600c003ff03f0

def z222 : W := mkw 0x0010034001081084 0x0002006800210210 0x983007c001181186 0xd30600f800230230

def z223 : W := mkw 0x030b0c42d70ebbfd 0xa06161885ae1d77f 0xbf0f0e07ff1fffff 0x77e1e1c0ffe3ffff

def z224 : W := mkw 0x000240c491049261 0x000048189220924c 0xa80ec9c791059e67 0xb501d938f220b3cc

def z225 : W := mkw 0x1fffcfffdfff9ff7 0xc3fff9fffbfff3fe 0xffffcfffffff9fff 0xfffff9fffffff3ff

def z226 : W := mkw 0x05b00f2002000900 0x00b601e400400120 0xf7f00ff81e001f86 0xfefe01ff03c003f0

def z227 : W := mkw 0x14a000480bb81d86 0x02940009017703b0 0xdff000001ff81f84 0xfbfe000003ff03f0

def z228 : W := mkw 0x27b93f2260000000 0x04f727e44c000000 0xa73f3e07e0000003 0x74e7e7c0fc000000

def z229 : W := mkw 0x080240cc91659661 0x41004819922cb2cc 0x8800c1c411e59e67 0x91001838823cb3cc

def z230 : W := mkw 0x020b000014060000 0x004160000280c000 0x970f00001e060005 0x72e1e00003c0c000

def z231 : W := mkw 0x27fffff7f70ebbfd 0xa4fffffefee1d77f 0xffffffffff1fffff 0xffffffffffe3ffff

def z232 : W := mkw 0x0800004801619420 0x41000009002c3284 0x0800000001e18000 0x01000000003c3000

def z233 : W := mkw 0x15b20f689fbe1fd7 0x82b641ed13f7c3fa 0xfff00ff81ffe1ffe 0xfffe01ff03ffc3ff

def z234 : W := mkw 0x06efa0481df75400 0x00ddf40903beea80 0xfffff9f81ffffe07 0xffffff3f03ffffc0

def z235 : W := mkw 0x17ffaf681fff5d86 0x02fff5ed03ffebb0 0xfffffff81fffff87 0xffffffff03fffff0

def z236 : W := mkw 0x01020c02d6060b51 0x802041805ac0c16a 0x30000e07fe061ffe 0x060001c0ffc0c3ff

def z237 : W := mkw 0x0a4fc097d4478271 0xc149f812fa88f04e 0x000fc007e0078079 0x0001f800fc00f00f

def z238 : W := mkw 0x0010538420000000 0x00020a7084000000 0x9031f7c4600611ff 0xd2063ef88c00c23f

def z239 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x57ff30001efa6000 0x6affe60003df4c00

def z240 : W := mkw 0x000040cc01209420 0x0000081980241284 0xe8c0c9fc11e59e67 0xbd18193f823cb3cc

def z241 : W := mkw 0x0846c0dd97679f71 0xc108d81bb2ecf3ee 0xf8cec9ff9fe79fff 0xbf19d93ff3fcf3ff

def z242 : W := mkw 0x0000000008900000 0x0000000001120000 0x180000001ff80004 0x0300000003ff0000

def z243 : W := mkw 0x05b00f2000000000 0x00b601e400000000 0x0730060000000000 0x40e600c000000000

def z244 : W := mkw 0x0044c0dd01201400 0x0008981ba0240280 0xe8cec9ff91e01e07 0xbd19d93ff23c03c0

def z245 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xbf3ffe07ff1fffff 0xf7e7ffc0ffe3ffff

def z246 : W := mkw 0x17ab0c2adeb60f53 0x82f561855bd6c1ea 0xf7cf0e3ffee61fff 0x7ef9e1c7ffdcc3ff

def z247 : W := mkw 0x04e4a00008d14000 0x009c9400011a2800 0xdff0f0001ff9e004 0xfbfe1e0003ff3c00

def z248 : W := mkw 0x25f4ffb520000000 0x04be9ff6a4000000 0xe7f0fff800000002 0xfcfe1fff00000000

def z249 : W := mkw 0x0000100020002008 0x2000020004000401 0x0001300060026018 0x000026000c004c03

def z250 : W := mkw 0x000040c401009020 0x0000081880201204 0x9801c7c4610791ff 0xd30038f88c20f23f

def z251 : W := mkw 0x17bb0f22de9e0bd7 0x82f761e45bd3c17a 0xb73f0e07fe1e1fff 0x76e7e1c0ffc3c3ff

def z252 : W := mkw 0x000200401ddff0ac 0x2000400803bbfe15 0x180000001ffff1fc 0x0300000003fffe3f

def z253 : W := mkw 0x27efac335cd74000 0x04fdf5866b9ae800 0xfffff83b9fffe005 0xffffff0773fffc00

def z254 : W := mkw 0x0002000010040000 0x0000400002008000 0x800e000010040005 0x3001c00002008000

def z255 : W := mkw 0x0b4fccdfd1659661 0x4169f99bfa2cb2cc 0xefcfcffff1e59e67 0xfdf9f9fffe3cb3cc

def z256 : W := mkw 0x2cf6f3fdb1659661 0x459ede7fb62cb2cc 0xe8fef9ff91e59e67 0xbd1fdf3ff23cb3cc

def z257 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x983007c4611811fe 0xd30600f88c23023f

def z258 : W := mkw 0x100000480bb81d86 0x02000009017703b0 0xf8c009f81ff81f86 0xbf18013f03ff03f0

def z259 : W := mkw 0x0000000080000241 0x0000000010000048 0x2000080780001e62 0x04000100f00003cc

def z260 : W := mkw 0x0844c0dd01619420 0x4108981ba02c3284 0xe8cec9ff81e18003 0xbd19d93ff03c3000

def z261 : W := mkw 0x05b00f2000000000 0x00b601e400000000 0xe7f00ff800000002 0xfcfe01ff00000000

def z262 : W := mkw 0x0046800090450241 0x0008d0001208a048 0xe8cec80791e59e67 0xbd19d900f23cb3cc

def z263 : W := mkw 0x07efac001ed74900 0x00fdf58003dae920 0xfffffe001fffff87 0xffffffc003fffff0

def z264 : W := mkw 0x05b00f2008900000 0x00b601e401120000 0xfff00ff81ff80006 0xfffe01ff03ff0000

def z265 : W := mkw 0x24e4a03100000000 0x049c940620000000 0x40c0003800000000 0x0818000700000000

def z266 : W := mkw 0x01000c02c2000b51 0x802001805840016a 0x2000080380000e00 0x04000100700001c0

def z267 : W := mkw 0x021b53c6f50eb2fd 0xa0436a78dea1d65f 0x983ff7c7e11ff1ff 0xd307fef8fc23fe3f

def z268 : W := mkw 0x020b000096060b51 0x8041600012c0c16a 0x970f00001e061ffd 0x72e1e00003c0c3ff

def z269 : W := mkw 0x001053cc2128b4ac 0x20020a7984251695 0xf8f1fffc71ffffff 0xff1e3fff8e3fffff

def z270 : W := mkw 0x37edac3b4ab00d02 0x06fdb587695601a0 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z271 : W := mkw 0x001013002008208c 0x2002026004010411 0x0000060060000198 0x000000c00c000033

def z272 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x0830f1c00119e000 0x81061e3800233c00

def z273 : W := mkw 0x0054d39520000000 0x000a9a72a4000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z274 : W := mkw 0x024fa00014474000 0x0049f4000288e800 0x983ff000011fe005 0xd307fe000023fc00

def z275 : W := mkw 0x0846c09590458261 0x4108d812b208b04c 0xa00ec80790059e67 0x3401d900f200b3cc

def z276 : W := mkw 0x0000409500000000 0x00000812a0000000 0x200009ff80000002 0x0400013ff0000000

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000000611fc 0x020000000000c23f

def z278 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x47cff0001ee7e001 0x28f9fe0003dcfc00

def z279 : W := mkw 0x001253c4b10cb2ed 0x20024a789621965d 0xb83fffc7f11fffff 0xf707fff8fe23ffff

def z280 : W := mkw 0x01000c4803201d00 0x00200189006403a0 0xffc00ff81fe01f86 0xfff801ff03fc03f0

def z281 : W := mkw 0x07efac025cd74000 0x00fdf5804b9ae800 0xfffffe07ffffe007 0xffffffc0fffffc00

def z282 : W := mkw 0x05f4cfb500000000 0x00be99f6a0000000 0xe7fecfff80000003 0xfcffd9fff0000000

def z283 : W := mkw 0x05b05fe42108b0ac 0x20b60bfc84211615 0xfff1fffc611ff1ff 0xfffe3fff8c23fe3f

def z284 : W := mkw 0x0b5fdfdff76fbffd 0xe16bfbfbfeedf7ff 0xffffffffffffffff 0xffffffffffffffff

def z285 : W := mkw 0x17efac281ef74d02 0x02fdf58503dee9a0 0xfffff8381fffee05 0xffffff0703fffdc0

def z286 : W := mkw 0x23195fb760000000 0x04632bf6ec000000 0xa70f0fffe0000003 0x74e1e1fffc000000

def z287 : W := mkw 0x0010034801281484 0x0002006900250290 0xf8f00ff811f81f86 0xff1e01ff023f03f0

def z288 : W := mkw 0x080040dd01209420 0x4100081ba0241284 0x000001f800000000 0x0000003f00000000

def z289 : W := mkw 0x0eefa0199cf74641 0x41ddf403339ee8c8 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z290 : W := mkw 0x0044c09500000000 0x00089812a0000000 0x000ec00780000001 0x0001d800f0000000

def z291 : W := mkw 0x03090c0242000900 0x0061218048400120 0xb70f0e07fe001f87 0x76e1e1c0ffc003f0

def z292 : W := mkw 0x100000480bb8bdae 0x22000009017717b5 0x180000001ffffffc 0x0300000003ffffff

def z293 : W := mkw 0x0044800000410000 0x0008900000082000 0x48c0c00001e18000 0x89181800003c3000

def z294 : W := mkw 0x07b90f2240000000 0x00f721e448000000 0xe7ff0fffe0000003 0xfcffe1fffc000000

def z295 : W := mkw 0x100200489fbe1fd7 0x8200400913f7c3fa 0x180000001ffe1ffc 0x0300000003ffc3ff

def z296 : W := mkw 0x0eefe0dd1df7d420 0x41ddfc1ba3befa84 0xdffff1f81fffe005 0xfbfffe3f03fffc00

def z297 : W := mkw 0x0844c0dd01619420 0x4108981ba02c3284 0xe8c0c9f811e19e06 0xbd18193f023c33c0

def z298 : W := mkw 0x01000c02c2000b51 0x802001805840016a 0xb7000e07fe001ffe 0x76e001c0ffc003ff

def z299 : W := mkw 0x030b0c0254060000 0x006161804a80c000 0xb70f0e07fe060007 0x76e1e1c0ffc0c000

def z300 : W := mkw 0x01000c0002000900 0x0020018000400120 0x20000e0000001f82 0x040001c0000003f0

def z301 : W := mkw 0x0044a00000414000 0x0008940000082800 0x0000f0000001e000 0x00001e0000003c00

def z302 : W := mkw 0x24f4f3b520000000 0x049e9e76a4000000 0xe0fef9ff80000003 0xbc1fdf3ff0000000

def z303 : W := mkw 0x1db04ffd8bb89fe7 0x43b609ffb17713fc 0xfff00fff9ff81fe6 0xfffe01fff3ff03fc

def z304 : W := mkw 0x180200489bfd9fe7 0x43004009137fb3fc 0x180000001ffd9fe4 0x0300000003ffb3fc

def z305 : W := mkw 0x000200001cd74000 0x00004000039ae800 0x000000001ee00000 0x0000000003dc0000

def z306 : W := mkw 0x04a0000008900000 0x0094000001120000 0xdff1f0001fffe005 0xfbfe3e0003fffc00

def z307 : W := mkw 0x07ffffc6ffdffbfd 0xa0fffff8dffbff7f 0xffffffc7ffffffff 0xfffffff8ffffffff

def z308 : W := mkw 0x27edac3340000000 0x04fdb58668000000 0xe7fff83b80000001 0xfcffff0770000000

def z309 : W := mkw 0x224df0976000a028 0x2449be12ec001405 0x000ff007e007e079 0x0001fe00fc00fc0f

def z310 : W := mkw 0x0eefe0dd9df7d661 0x41ddfc1bb3befacc 0xefcec9ff9fe59e67 0xbdf9d93ff3fcb3cc

def z311 : W := mkw 0x234dfc9760000000 0x0469bf92ec000000 0xa70ffe07e0000003 0x74e1ffc0fc000000

def z312 : W := mkw 0x2ffdffffe1209661 0x45ffbffffc2412cc 0xe7ffffffe0001e63 0xfcfffffffc0003cc

def z313 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x370f0e03fe020f98 0x66e1e1c07fc041f3

def z314 : W := mkw 0x07efac02d6060b51 0x80fdf5805ac0c16a 0xf7fffe07fe061fff 0xfeffffc0ffc0c3ff

def z315 : W := mkw 0x020b0002d6060b51 0x804160005ac0c16a 0x100f0007fe061ffd 0x0201e000ffc0c3ff

def z316 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xffffffffe11fe007 0xfffffffffc23fc00

def z317 : W := mkw 0x37fdaf7b4bb81d86 0x06ffb5ef697703b0 0xfffe0ffb9ff81f86 0xffffc1ff73ff03f0

def z318 : W := mkw 0x27ffffb77cd74000 0x04fffff6ef9ae800 0xe7fffffffee00003 0xfcffffffffdc0000

def z319 : W := mkw 0x2fffffbff0650641 0x45fffff7fe0ca0c8 0xe7fffffff0e00e03 0xfcfffffffe1c01c0

def z320 : W := mkw 0x0a4fc0dfd5679671 0xc149f81bfaacf2ce 0xe8cfc9fff1e79e7f 0xbd19f93ffe3cf3cf

def z321 : W := mkw 0x000050842000a028 0x20000a1084001405 0x9831f004611fe07d 0xd3063e008c23fc0f

def z322 : W := mkw 0x1df6cffd9bfd9fe7 0x43bed9ffb37fb3fc 0xfffecfff9ffd9fe7 0xffffd9fff3ffb3fc

def z323 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x000001c000000000 0x0000003800000000

def z324 : W := mkw 0x07bb0f22d6060b51 0x80f761e45ac0c16a 0xf7ff0ffffe061fff 0xfeffe1ffffc0c3ff

def z325 : W := mkw 0x030b5c86f606ab79 0xa0616b90dec0d56f 0xb70ffe07fe07ffff 0x76e1ffc0ffc0ffff

def z326 : W := mkw 0x0000000008d14000 0x00000000011a2800 0x0800000001f9e000 0x01000000003f3c00

def z327 : W := mkw 0x27fdffb762000900 0x04ffbff6ec400120 0xf7fffffffe001f87 0xfeffffffffc003f0

def z328 : W := mkw 0x001053c421081084 0x00020a7884210210 0x9831f7c461181187 0xd3063ef88c230230

def z329 : W := mkw 0x15a00c280ab00d02 0x02b40185015601a0 0xfff008381ff80e04 0xfffe010703ff01c0

def z330 : W := mkw 0x27fdfff76108b0ac 0x24ffbffeec211615 0xffffffffe11ff1ff 0xfffffffffc23fe3f

def z331 : W := mkw 0x0ce6e0dd99f5d661 0x419cdc1bb33ebacc 0xe8fef9ff91fdfe67 0xbd1fdf3ff23fbfcc

def z332 : W := mkw 0x06b933002c9a608c 0x20d7266005934c11 0x173136006e1a6198 0x42e626c00dc34c33

def z333 : W := mkw 0x17ffaf6adfff5fd7 0x82fff5ed5bffebfa 0xffffffffffffffff 0xffffffffffffffff

def z334 : W := mkw 0x15f68f681bfd1d86 0x02bed1ed037fa3b0 0xfffecff81ffd9f87 0xffffd9ff03ffb3f0

def z335 : W := mkw 0x2154dfb760000000 0x042a9bf6ec000000 0xe0cecfffe0000003 0xbc19d9fffc000000

def z336 : W := mkw 0x27fdffb768900000 0x04ffbff6ed120000 0xfffffffffff80007 0xffffffffffff0000

def z337 : W := mkw 0x27fdfff761009020 0x04ffbffeec201204 0xefffffffe1059067 0xfdfffffffc20b20c

def z338 : W := mkw 0x17b90f6a4bb81d86 0x02f721ed497703b0 0xffff0ffffff81f87 0xffffe1ffffff03f0

def z339 : W := mkw 0x030b0c02ded74b51 0x806161805bdae96a 0xbf0f0e07ffffffff 0x77e1e1c0ffffffff

def z340 : W := mkw 0x0000000002000900 0x0000000000400120 0x100000001e001f84 0x0200000003c003f0

def z341 : W := mkw 0x11100f2002080986 0x022201e400410130 0x0000060000000180 0x000000c000000030

def z342 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x6ff009f81ff80e00 0xadfe013f03ff01c0

def z343 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff1fff81fffff87 0xfffe3fff03fffff0

def z344 : W := mkw 0x01000c0000000000 0x0020018000000000 0xa7000e0000000002 0x74e001c000000000

def z345 : W := mkw 0x05b05fa420000000 0x00b60bf484000000 0xe7f1fffc60000003 0xfcfe3fff8c000000

def z346 : W := mkw 0x14a0002808b00402 0x0294000501160080 0x40c0003800e00000 0x08180007001c0000

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8c0000011e00004 0xb9180000023c0000

def z348 : W := mkw 0x27ffffb770450000 0x04fffff6ee08a000 0xeffffffff1e58007 0xfdfffffffe3cb000

def z349 : W := mkw 0x06efa00014474000 0x00ddf4000288e800 0xc7fff0000007e001 0xf8fffe000000fc00

def z350 : W := mkw 0x0846d095b045a269 0x6108da12b608b44d 0x000ff007e007e079 0x0001fe00fc00fc0f

def z351 : W := mkw 0x04b053c42998b0ac 0x20960a7885331615 0xdff1f7c47ffff1ff 0xfbfe3ef88ffffe3f

def z352 : W := mkw 0x0eefa0489df7d661 0x41ddf40913befacc 0xdffff0001ffffe65 0xfbfffe0003ffffcc

def z353 : W := mkw 0x020b0002d4060251 0x804160005a80c04a 0x970f0007fe06007d 0x72e1e000ffc0c00f

def z354 : W := mkw 0x020b000014060000 0x004160000280c000 0x000f000000060001 0x0001e0000000c000

def z355 : W := mkw 0x000000000000a028 0x2000000000001405 0x000000000007e078 0x000000000000fc0f

def z356 : W := mkw 0x37fdffbf6ab00d02 0x06ffbff7ed5601a0 0xe7fffffffee00e03 0xfcffffffffdc01c0

def z357 : W := mkw 0x0802000090458261 0x410040001208b04c 0x0000000000058060 0x000000000000b00c

def z358 : W := mkw 0x0846801990650641 0x4108d003320ca0c8 0xe0ce083f90e41e67 0x3c19c107f21c83cc

def z359 : W := mkw 0x0846c0dd916db6ed 0x6108d81bb22db6dd 0xf8cec9ff91ffffff 0xbf19d93ff23fffff

def z360 : W := mkw 0x04e4a00008d14000 0x009c9400011a2800 0xd8f1f00001ffe005 0xdb1e3e00003ffc00

def z361 : W := mkw 0x07efac02ded74b51 0x80fdf5805bdae96a 0xf7cf0e07fee61fff 0x7ef9e1c0ffdcc3ff

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0x9831f604611ff1ff 0xd3063ec08c23fe3f

def z363 : W := mkw 0x04f4f3c429d9f0ac 0x209e9e78853b3e15 0x48f0f1c001f9e000 0x891e1e38003f3c00

def z364 : W := mkw 0x0010034001081084 0x0002006800210210 0x000007c000001182 0x000000f800000230

def z365 : W := mkw 0x0046800010450000 0x0008d0000208a000 0xd8fff00011ffe005 0xfb1ffe00023ffc00

def z366 : W := mkw 0x14b003680bb81d86 0x0296006d017703b0 0x58f001f81ff81f84 0x8b1e003f03ff03f0

def z367 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0xe8c009f811e59e66 0xbd18013f023cb3cc

def z368 : W := mkw 0x21105ff76108b0ac 0x24220bfeec211615 0xb831ffffe11ff1ff 0xd7063ffffc23fe3f

def z369 : W := mkw 0x020b000014060000 0x004160000280c000 0x970f06047e0611ff 0x72e1e0c08fc0c23f

def z370 : W := mkw 0x01000c0240000000 0x0020018048000000 0x20000e07e0000002 0x040001c0fc000000

def z371 : W := mkw 0x24b0332020000000 0x0496066404000000 0x0030300000000000 0x0006060000000000

def z372 : W := mkw 0x0846c09590458261 0x4108d812b208b04c 0xe0cec9ff80058063 0xbc19d93ff000b00c

def z373 : W := mkw 0x15b01f202a98298e 0x22b603e405530531 0x173136006e1a6198 0x42e626c00dc34c33

def z374 : W := mkw 0x24f4f3b528d14000 0x049e9e76a51a2800 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z375 : W := mkw 0x1de6ccfd9bf59f63 0x43bcd99fb37eb3ec 0xefcec9ff9fe59e67 0xbdf9d93ff3fcb3cc

def z376 : W := mkw 0x27b93f2266020910 0x84f727e44cc04122 0x173136006e020198 0x42e626c00dc04033

def z377 : W := mkw 0x17b92f680fba5d86 0x02f725ed01f74bb0 0xfff13ff81ffa7f86 0xfffe27ff03ff4ff0

def z378 : W := mkw 0x14b0036809b81486 0x0296006d01370290 0xd8f007f801f81186 0xdb1e00ff003f0230

def z379 : W := mkw 0x06efa00014060000 0x00ddf4000280c000 0xd7fff0001e060005 0xfafffe0003c0c000

def z380 : W := mkw 0x03090c0246020910 0x8061218048c04122 0xb7010e007e021f9e 0x76e021c00fc043f3

def z381 : W := mkw 0x15f4cffd0bb81d86 0x02be99ffa17703b0 0xfffecfff9ff81f87 0xffffd9fff3ff03f0

def z382 : W := mkw 0x0856d3d5b14db2ed 0x610ada7ab629b65d 0x983ff7c7e11ff1ff 0xd307fef8fc23fe3f

def z383 : W := mkw 0x0010034001081084 0x0002006800210210 0x083001c001180000 0x8106003800230000

def z384 : W := mkw 0x1df68f799bfd1fc7 0x43bed1ef337fa3f8 0xfffe0ffb9ff81f86 0xffffc1ff73ff03f0

def z385 : W := mkw 0x37b93f226a980986 0x06f727e44d530130 0x173136006e180180 0x42e626c00dc30030

def z386 : W := mkw 0x0fefecdfdff7df71 0xc1fdfd9bfbfefbee 0xffffffffffffffff 0xffffffffffffffff

def z387 : W := mkw 0x100000080ab00d02 0x02000001015601a0 0x000000001ee00e00 0x0000000003dc01c0

def z388 : W := mkw 0x15b00f680bb8bdae 0x22b601ed017717b5 0xfff00ff81ffffffe 0xfffe01ff03ffffff

def z389 : W := mkw 0x0209000000000000 0x0041200000000000 0x870f000000000001 0x70e1e00000000000

def z390 : W := mkw 0x04e6a0001cd74000 0x009cd400039ae800 0x58f0f0001fffe004 0x8b1e1e0003fffc00

def z391 : W := mkw 0x235dffb760000000 0x046bbff6ec000000 0x200fffffe0000003 0x0401fffffc000000

def z392 : W := mkw 0x000200009ed74b51 0x8000400013dae96a 0x180000001ffffffc 0x0300000003ffffff

def z393 : W := mkw 0x0846c0dd11659420 0x4108d81ba22cb284 0xc8cec1f811e58005 0xb919d83f023cb000

def z394 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x4ffef0001ff9e000 0xa9ffde0003ff3c00

def z395 : W := mkw 0x0800004881209661 0x41000009102412cc 0x0000000000001e60 0x00000000000003cc

def z396 : W := mkw 0x05a00c2000000000 0x00b4018400000000 0x67c0083800000000 0x2cf8010700000000

def z397 : W := mkw 0x0946ccdfd3659f71 0xc128d99bfa6cb3ee 0xe8cecffff1e59fff 0xbd19d9fffe3cb3ff

def z398 : W := mkw 0x06eda00008900000 0x00ddb40001120000 0xdffff0001ff80005 0xfbfffe0003ff0000

def z399 : W := mkw 0x1cf6c3fd99fd96e7 0x439ed87fb33fb2dc 0xe8fec9ff91fd9e67 0xbd1fd93ff23fb3cc

def z400 : W := mkw 0x130b0c4adfbe1fd7 0x826161895bf7c3fa 0xbf0f0e07fffe1fff 0x77e1e1c0ffffc3ff

def z401 : W := mkw 0x000000400108b0ac 0x2000000800211615 0x98010604611ff1ff 0x530020c08c23fe3f

def z402 : W := mkw 0x000040c401009020 0x0000081880201204 0x9831f1c4011ff067 0xd3063e388023fe0c

def z403 : W := mkw 0x1846c0dd9bfd9fe7 0x4308d81bb37fb3fc 0xf8cec9ff9ffd9fe7 0xbf19d93ff3ffb3fc

def z404 : W := mkw 0x27fdfff761081084 0x04ffbffeec210210 0xffffffffe1181187 0xfffffffffc230230

def z405 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x1830f1c0011ff1fc 0x83061e380023fe3f

def z406 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xd7cf00001ee60005 0x7af9e00003dcc000

def z407 : W := mkw 0x201053b520000000 0x04020a76a4000000 0x000001f800000000 0x0000003f00000000

def z408 : W := mkw 0x2fffffb7f0458261 0x45fffff6fe08b04c 0xe7ffffffe0058063 0xfcfffffffc00b00c

def z409 : W := mkw 0x05a00c000a900900 0x00b4018001520120 0xfff00e001ff81f86 0xfffe01c003ff03f0

def z410 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0xa80e080791e59e67 0x3501c100f23cb3cc

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001f0000007e001 0x00003e000000fc00

def z412 : W := mkw 0x001013002008208c 0x2002026004010411 0x0030300000186000 0x0006060000030c00

def z413 : W := mkw 0x04f4f3c429d9f0ac 0x209e9e78853b3e15 0xd8f1f7c461fff1ff 0xdb1e3ef88c3ffe3f

def z414 : W := mkw 0x27b93f226c924000 0x04f727e44d924800 0x173136006e1a6000 0x42e626c00dc34c00

def z415 : W := mkw 0x17bb5feeffbebfff 0xa2f76bfddff7d7ff 0xffffffffffffffff 0xffffffffffffffff

def z416 : W := mkw 0x2fefecffd1659661 0x45fdfd9ffa2cb2cc 0xefcec9ff91e59e67 0xbdf9d93ff23cb3cc

def z417 : W := mkw 0x01105fc6e308bbfd 0xa0220bf8dc61177f 0xb831ffc7e11fffff 0xd7063ff8fc23ffff

def z418 : W := mkw 0x04a200001cd74000 0x00944000039ae800 0xdff000001fffe004 0xfbfe000003fffc00

def z419 : W := mkw 0x24f4f3b520000000 0x049e9e76a4000000 0xc0f1f7fc60000003 0xd81e3eff8c000000

def z420 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xa70e08079e041e67 0x34e1c100f3c083cc

def z421 : W := mkw 0x024fa002d4474251 0x8049f4005a88e84a 0x000ff007e007e079 0x0001fe00fc00fc0f

def z422 : W := mkw 0x000000400108b0ac 0x2000000800211615 0x080000000119e000 0x0100000000233c00

def z423 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x67c00ff81ee01f82 0x2cf801ff03dc03f0

def z424 : W := mkw 0x06fdf38420000000 0x00dfbe7084000000 0xc7fff7c460000003 0xf8fffef88c000000

def z425 : W := mkw 0x15b20f689bbc1fc7 0x02b641ed137783f8 0xfffe0fff9ffc1fe7 0xffffc1fff3ff83fc

def z426 : W := mkw 0x0209000240000000 0x0041200048000000 0x000f0007e0000001 0x0001e000fc000000

def z427 : W := mkw 0x030b4cc6d7069b71 0x80616998dae0d36e 0xbf0fcfc7ff079fff 0xf7e1f9f8ffe0f3ff

def z428 : W := mkw 0x101003480bb81d86 0x02020069017703b0 0x983007c01ff81f86 0xd30600f803ff03f0

def z429 : W := mkw 0x27ffffb774060000 0x04fffff6ee80c000 0xf7fffffffe060007 0xfeffffffffc0c000

def z430 : W := mkw 0x14b0036809b81486 0x0296006d01370290 0xdff001f81ff80004 0xfbfe003f03ff0000

def z431 : W := mkw 0x2044f09520000000 0x04089e12a4000000 0x0000f00000000000 0x00001e0000000000

def z432 : W := mkw 0x0802000890650641 0x41004001120ca0c8 0x0000000010e00e00 0x00000000021c01c0

def z433 : W := mkw 0x24f4f3f52108b0ac 0x249e9e7ea4211615 0x48f0f1f80119e000 0x891e1e3f00233c00

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0c009f800000002 0xbc18013f00000000

def z435 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001060460000003 0x500020c08c000000

def z436 : W := mkw 0x27fdbf2260000000 0x04ffb7e44c000000 0xc7fff60060000001 0xf8fffec00c000000

def z437 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x170f0607ee0601f9 0x42e1e0c0fdc0c03f

def z438 : W := mkw 0x0010538420000000 0x00020a7084000000 0x0030f1c000000000 0x80061e3800000000

def z439 : W := mkw 0x37fdffff69b81486 0x06ffbfffed370290 0xefffffffe1f80003 0xfdfffffffc3f0000

def z440 : W := mkw 0x27fdbf3360000000 0x04ffb7e66c000000 0x67ff3e3be0000000 0x6cffe7c77c000000

def z441 : W := mkw 0x001053842008208c 0x20020a7084010411 0x9031f7c4601a619b 0xd2063ef88c034c33

def z442 : W := mkw 0x0802004897679f71 0xc100400912ecf3ee 0x180000001fe79ffc 0x0300000003fcf3ff

def z443 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x073ff607e0000001 0x40e7fec0fc000000

def z444 : W := mkw 0x0002000096060b51 0x8000400012c0c16a 0xb00e08079e061fff 0x3601c100f3c0c3ff

def z445 : W := mkw 0x000040c401009020 0x0000081880201204 0x0800c1c001018000 0x8100183800203000

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x9001000000060005 0x520020000000c000

def z447 : W := mkw 0x080240dd91249661 0x4100481bb22492cc 0xa00e09ff90041e67 0x3401c13ff20083cc

def z448 : W := mkw 0x27ffffb7f4060251 0x84fffff6fe80c04a 0xe7ffffffe006007b 0xfcfffffffc00c00f

def z449 : W := mkw 0x27fdffb76c924000 0x04ffbff6ed924800 0xf7ffffffee1a6003 0xfefffffffdc34c00

def z450 : W := mkw 0x0000004801201400 0x0000000900240280 0x200009f800001e02 0x0400013f000003c0

def z451 : W := mkw 0x001013402108b0ac 0x2002026804211615 0x18313600611ff1fc 0x430626c00c23fe3f

def z452 : W := mkw 0x15a00c280ab00d02 0x02b40185015601a0 0xf7c00e381ee01f86 0x7ef801c703dc03f0

def z453 : W := mkw 0x020b00001cd74000 0x00416000039ae800 0x9f0f00001fffe005 0x73e1e00003fffc00

def z454 : W := mkw 0x000050c42100b028 0x20000a1884201605 0x8801f1c46107f07f 0x91003e388c20fe0f

def z455 : W := mkw 0x17ffaf201edf4986 0x02fff5e403dbe930 0xdffff6001fffe185 0xfbfffec003fffc30

def z456 : W := mkw 0x34f4f3fd29b81486 0x069e9e7fa5370290 0x48f0f1f801f80000 0x891e1e3f003f0000

def z457 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x68cec9fb91e18e00 0xad19d93f723c31c0

def z458 : W := mkw 0x27fdfff76108b0ac 0x24ffbffeec211615 0xefffffffe119e003 0xfdfffffffc233c00

def z459 : W := mkw 0x21105fb760000000 0x04220bf6ec000000 0xa031ffffe0000003 0xd4063ffffc000000

def z460 : W := mkw 0x27ffffb7f0040241 0x04fffff6fe008048 0xe7fffffff0041e67 0xfcfffffffe0083cc

def z461 : W := mkw 0x000050842000a028 0x20000a1084001405 0x9001f6046007f1ff 0x52003ec08c00fe3f

def z462 : W := mkw 0x224ff09774474000 0x0449fe12ee88e800 0x000ff007e007e001 0x0001fe00fc00fc00

def z463 : W := mkw 0x0846c0d591459261 0x4108d81ab228b24c 0x880ec1c781059067 0x9101d838f020b20c

def z464 : W := mkw 0x27efac33d6060b51 0x84fdf5867ac0c16a 0xf7cf0e3ffe061fff 0x7ef9e1c7ffc0c3ff

def z465 : W := mkw 0x27ffffb7fed74b51 0x84fffff6ffdae96a 0xffffffffffffffff 0xffffffffffffffff

def z466 : W := mkw 0x01100f2000000000 0x002201e400000000 0x20000ff800000002 0x040001ff00000000

def z467 : W := mkw 0x27fffff77ddff0ac 0x24fffffeefbbfe15 0xfffffffffffff1ff 0xfffffffffffffe3f

def z468 : W := mkw 0x2ffffffff16db6ed 0x65fffffffe2db6dd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z469 : W := mkw 0x020b000014060000 0x004160000280c000 0x070e00001e000000 0x20e1c00003c00000

def z470 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x200ec9ff80059e63 0x0401d93ff000b3cc

def z471 : W := mkw 0x17b92f200e9a4986 0x02f725e401d34930 0x173136000e1a6180 0x42e626c001c34c30

def z472 : W := mkw 0x04a0000008900000 0x0094000001120000 0x47c000001ee00000 0x28f8000003dc0000

def z473 : W := mkw 0x0b0b4cdfd7269f71 0xc161699bfae4d3ee 0xb70f0ffffe061fff 0x76e1e1ffffc0c3ff

def z474 : W := mkw 0x0844c0dd01619420 0x4108981ba02c3284 0xc8c0c1fc01e59067 0x9918183f803cb20c

def z475 : W := mkw 0x21000c3340000000 0x0420018668000000 0x2000083b80000000 0x0400010770000000

def z476 : W := mkw 0x0002000094060251 0x800040001280c04a 0x0000000000060078 0x000000000000c00f

def z477 : W := mkw 0x0b0b0c4ad7679f71 0xc16161895aecf3ee 0xbf0f0e07ffe79fff 0x77e1e1c0fffcf3ff

def z478 : W := mkw 0x14b053ec29b8b4ae 0x22960a7d85371695 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z479 : W := mkw 0x07fdaf2000000000 0x00ffb5e400000000 0xe7fffff800000003 0xfcffffff00000000

def z480 : W := mkw 0x000050842000a028 0x20000a1084001405 0x0000f0000001e000 0x00001e0000003c00

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000400041067 0x100000008000820c

def z482 : W := mkw 0x001013402108308c 0x2002026804210611 0x983137c0611a719e 0xd30626f80c234e33

def z483 : W := mkw 0x2a4ff097f0458261 0x4549fe12fe08b04c 0x000ff007e0058061 0x0001fe00fc00b00c

def z484 : W := mkw 0x15b00f280ab00d02 0x02b601e5015601a0 0xe7f00ff81ee00e02 0xfcfe01ff03dc01c0

def z485 : W := mkw 0x0854d3dd2169b4ac 0x610a9a7ba42d3695 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z486 : W := mkw 0x07a92c024e924910 0x80f5258049d24922 0x173136006e1a6198 0x42e626c00dc34c33

def z487 : W := mkw 0x0b4f8c1bd6670f51 0xc169f1837acce1ea 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z488 : W := mkw 0x0000000006020910 0x8000000000c04122 0x100000000e020198 0x0200000001c04033

def z489 : W := mkw 0x04b0032000000000 0x0096006400000000 0x40f001f800000000 0x881e003f00000000

def z490 : W := mkw 0x024fa0001cd74000 0x0049f400039ae800 0x180ff0001fffe005 0x0301fe0003fffc00

def z491 : W := mkw 0x15a00c680bb81d86 0x02b4018d017703b0 0x7fc008381ff81f84 0x2ff8010703ff03f0

def z492 : W := mkw 0x001253c43ddff0ac 0x20024a7887bbfe15 0x9831f7c47ffff1ff 0xd3063ef88ffffe3f

def z493 : W := mkw 0x0ce6c0dd99f59661 0x419cd81bb33eb2cc 0xfffec9ff9ffd9e67 0xffffd93ff3ffb3cc

def z494 : W := mkw 0x06ffb3003cdf608c 0x20dff660079bec11 0xdffff6007fffe19d 0xfbfffec00ffffc33

def z495 : W := mkw 0x00020040970ebbfd 0xa000400812e1d77f 0x180000001f1ffffc 0x0300000003e3ffff

def z496 : W := mkw 0x06a920000c924000 0x00d5240001924800 0x9f31f0000f1fe005 0xd3e63e0001e3fc00

def z497 : W := mkw 0x131b0f6ad72e1fd7 0x826361ed5ae5c3fa 0xb70f0ffffe061fff 0x76e1e1ffffc0c3ff

def z498 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x180007c4611ff1fe 0x030000f88c23fe3f

def z499 : W := mkw 0x001053842000a028 0x20020a7084001405 0x8031f7c46007e07b 0xd0063ef88c00fc0f

def z500 : W := mkw 0x0800409580008261 0x41000812b000104c 0x0000000780000060 0x00000000f000000c

def z501 : W := mkw 0x020b0002d4060251 0x804160005a80c04a 0xa00f0807f0061e7f 0x3401e100fe00c3cf

def z502 : W := mkw 0x06eda0000c924000 0x00ddb40001924800 0xd7fff0000e1a6001 0xfafffe0001c34c00

def z503 : W := mkw 0x06fff3c43ddff0ac 0x20dffe7887bbfe15 0xdffff1c01fffe005 0xfbfffe3803fffc00

def z504 : W := mkw 0x37fdffff6bb8bdae 0x26ffbfffed7717b5 0xffffffffffffffff 0xffffffffffffffff

def z505 : W := mkw 0x0002000096060b51 0x8000400012c0c16a 0x900106047e061fff 0x520020c08fc0c3ff

def z506 : W := mkw 0x04e4a00000000000 0x009c940000000000 0x40f0f00000000000 0x881e1e0000000000

def z507 : W := mkw 0x100200481fff5d86 0x0200400903ffebb0 0x180000001fffff84 0x0300000003fffff0

def z508 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x173ff0000e1fe001 0x42e7fe0001c3fc00

def z509 : W := mkw 0x224df09760000000 0x0449be12ec000000 0xe0cff9ffe0000003 0xbc19ff3ffc000000

def z510 : W := mkw 0x03090c0246020910 0x8061218048c04122 0x970106046e0611ff 0x52e020c08dc0c23f

def z511 : W := mkw 0x080040dd81209661 0x4100081bb02412cc 0xe8c009ff91e01e66 0xbd18013ff23c03cc

def z512 : W := mkw 0x29105fffe1209661 0x45220bfffc2412cc 0x20000fffe0001e62 0x040001fffc0003cc

def z513 : W := mkw 0x225df3d76108b0ac 0x244bbe7aec211615 0x983ff7c7e11ff1ff 0xd307fef8fc23fe3f

def z514 : W := mkw 0x35b05fff6bb81d86 0x06b60bffed7703b0 0xfff00ffffff81f86 0xfffe01ffffff03f0

def z515 : W := mkw 0x000000400108b0ac 0x2000000800211615 0x00000000000011f8 0x000000000000023f

def z516 : W := mkw 0x01000c0002000900 0x0020018000400120 0xb7010e047e061fff 0x76e021c08fc0c3ff

def z517 : W := mkw 0x0209000244020010 0x8041200048804002 0x0001000060020018 0x000020000c004003

def z518 : W := mkw 0x17ab0c2adeb60f53 0x82f561855bd6c1ea 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z519 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffe00001ff80004 0xfbffc00003ff0000

def z520 : W := mkw 0x06ab20001cd74000 0x00d56400039ae800 0x1f3130001fffe004 0x43e6260003fffc00

def z521 : W := mkw 0x0000004001009020 0x0000000800201204 0x0800000001059064 0x010000000020b20c

def z522 : W := mkw 0x06ab00001c960000 0x00d560000392c000 0xdfff00001ffe0005 0xfbffe00003ffc000

def z523 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x103137c4601a71fa 0x420626f88c034e3f

def z524 : W := mkw 0x0002000096060b51 0x8000400012c0c16a 0x000000001e000e00 0x0000000003c001c0

def z525 : W := mkw 0x0010538420000000 0x00020a7084000000 0x000007c460000002 0x000000f88c000000

def z526 : W := mkw 0x15b00f6809b81486 0x02b601ed01370290 0xeff00ff801f80002 0xfdfe01ff003f0000

def z527 : W := mkw 0x37fdffb76a980986 0x06ffbff6ed530130 0xf7ffffffee180183 0xfefffffffdc30030

def z528 : W := mkw 0x27ffbf227cd74000 0x04fff7e44f9ae800 0xdffff6007fffe005 0xfbfffec00ffffc00

def z529 : W := mkw 0x0844c0dd81619661 0x4108981bb02c32cc 0x68c0c9ff81e19e62 0x8d18193ff03c33cc

def z530 : W := mkw 0x06eda00008d14000 0x00ddb400011a2800 0xcffff00001f9e001 0xf9fffe00003f3c00

def z531 : W := mkw 0x37fdffff63281d86 0x06ffbfffec6503b0 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z532 : W := mkw 0x07edac0240000000 0x00fdb58048000000 0xe7fffe07e0000003 0xfcffffc0fc000000

def z533 : W := mkw 0x0a4fe0959447c261 0x4149fc12b288f84c 0x000ff0078007e061 0x0001fe00f000fc0c

def z534 : W := mkw 0x04a0000000000000 0x0094000000000000 0xc7f0000000000000 0xf8fe000000000000

def z535 : W := mkw 0x04e4a00008d14000 0x009c9400011a2800 0x40c0000000e00000 0x08180000001c0000

def z536 : W := mkw 0x17ffffec3ffffdae 0x22fffffd87ffffb5 0xfffffffc7fffffff 0xffffffff8fffffff

def z537 : W := mkw 0x1df6dffdbbfdbfef 0x63bedbffb77fb7fd 0xffffffffffffffff 0xffffffffffffffff

def z538 : W := mkw 0x020b000094060241 0x004160001280c048 0xb70f08079e061e67 0x76e1e100f3c0c3cc

def z539 : W := mkw 0x0800001980200641 0x41000003300400c8 0x2000083b80000e00 0x04000107700001c0

def z540 : W := mkw 0x2956dffff1659661 0x452adbfffe2cb2cc 0xe8cecffff1e59e67 0xbd19d9fffe3cb3cc

def z541 : W := mkw 0x034dcc9740000000 0x0069b992e8000000 0xe7cfcfffe0000003 0xfcf9f9fffc000000

def z542 : W := mkw 0x26eff0977cd74000 0x04ddfe12ef9ae800 0xdffff007ffffe005 0xfbfffe00fffffc00

def z543 : W := mkw 0x11000c480bb81d86 0x02200189017703b0 0xbf000e001ff81f86 0x77e001c003ff03f0

def z544 : W := mkw 0x06b973c42d9af0ac 0x20d72e7885b35e15 0x9f31f7c46f1ff1ff 0xd3e63ef88de3fe3f

def z545 : W := mkw 0x0000000000000000 0x0000000000000000 0x0830f0000119e000 0x81061e0000233c00

def z546 : W := mkw 0x06eda00000000000 0x00ddb40000000000 0xdffff000011fe005 0xfbfffe000023fc00

def z547 : W := mkw 0x0044800000000000 0x0008900000000000 0xc0cec00000000001 0xb819d80000000000

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000080010001e06 0x34000100020003c0

def z549 : W := mkw 0x11100f6803281d86 0x022201ed006503b0 0xe8c00ff811e01f86 0xbd1801ff023c03f0

def z550 : W := mkw 0x11105fec2328bdae 0x22220bfd846517b5 0xb831fffc611fffff 0xd7063fff8c23ffff

def z551 : W := mkw 0x0000004001001000 0x0000000800200200 0x880001c001001006 0x9100003800200200

def z552 : W := mkw 0x0209000004020000 0x0041200000804000 0x170100000e020000 0x42e0200001c04000

def z553 : W := mkw 0x27ffffb774474000 0x04fffff6ee88e800 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z554 : W := mkw 0x27bb3f22f6060b51 0x84f767e45ec0c16a 0xb73f3e07fe061fff 0x76e7e7c0ffc0c3ff

def z555 : W := mkw 0x27ffffb7f6060b51 0x84fffff6fec0c16a 0xe7fffffffe000e03 0xfcffffffffc001c0

def z556 : W := mkw 0x27b97fe66108b0ac 0x24f72ffccc211615 0x9f31f7c4611ff1ff 0xd3e63ef88c23fe3f

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000060000001186 0x520000c000000230

def z558 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x8831f7c46119e003 0xd1063ef88c233c00

def z559 : W := mkw 0x06fdf3c42108b0ac 0x20dfbe7884211615 0xdffff7c4611ff1ff 0xfbfffef88c23fe3f

def z560 : W := mkw 0x0209200004024000 0x0041240000804800 0x0001300000026000 0x0000260000004c00

def z561 : W := mkw 0x11105fec2328bdae 0x22220bfd846517b5 0x20000ffc60001ffa 0x040001ff8c0003ff

def z562 : W := mkw 0x07efac02ded74b51 0x80fdf5805bdae96a 0x67ce08039ee00e00 0x2cf9c10073dc01c0

def z563 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x9831f1c0011fe005 0xd3063e380023fc00

def z564 : W := mkw 0x26edf09760000000 0x04ddbe12ec000000 0xc7fff007e0000001 0xf8fffe00fc000000

def z565 : W := mkw 0x25b05fb760000000 0x04b60bf6ec000000 0xe7f00fffe0000002 0xfcfe01fffc000000

def z566 : W := mkw 0x001043c4010890a4 0x0002087880211214 0x9830c7c4011d91e7 0xd30618f88023b23c

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x9830000001180004 0xd306000000230000

def z568 : W := mkw 0x26fdf3b760000000 0x04dfbe76ec000000 0x40fff1ffe0000001 0x881ffe3ffc000000

def z569 : W := mkw 0x06ab20001c964000 0x00d564000392c800 0x973f30001e1e6005 0x72e7e60003c3cc00

def z570 : W := mkw 0x001253c4b70ebbfd 0xa0024a7896e1d77f 0x9831f7c47f1fffff 0xd3063ef88fe3ffff

def z571 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x200f0e07e0061ffb 0x0401e1c0fc00c3ff

def z572 : W := mkw 0x2000509760000000 0x04000a12ec000000 0x00000007e0000000 0x00000000fc000000

def z573 : W := mkw 0x0844c0dd81209661 0x4108981bb02412cc 0xe0cec9ff80001e63 0xbc19d93ff00003cc

def z574 : W := mkw 0x17bb0f681fbe1d86 0x02f761ed03f7c3b0 0xffff0ff81ffe1f87 0xffffe1ff03ffc3f0

def z575 : W := mkw 0x0a4fe0dd9567d661 0x4149fc1bb2acfacc 0xe8cff9ff91e7fe67 0xbd19ff3ff23cffcc

def z576 : W := mkw 0x024da00000000000 0x0049b40000000000 0x000ff00000000001 0x0001fe0000000000

def z577 : W := mkw 0x07efac025ed74910 0x80fdf5804bdae922 0xdffff6007fffe19d 0xfbfffec00ffffc33

def z578 : W := mkw 0x03195fc66108b0ac 0x20632bf8cc211615 0xbf3fffc7e11ff1ff 0xf7e7fff8fc23fe3f

def z579 : W := mkw 0x0ce4e0dd09f1d420 0x419c9c1ba13e3a84 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z580 : W := mkw 0x231b5fb7f6060b51 0x84636bf6fec0c16a 0xb70f0ffffe061fff 0x76e1e1ffffc0c3ff

def z581 : W := mkw 0x16ffa3681dff5486 0x02dff46d03bfea90 0xdffff1f81fffe005 0xfbfffe3f03fffc00

def z582 : W := mkw 0x15b00f6803281d86 0x02b601ed006503b0 0xe7f00ff800001f82 0xfcfe01ff000003f0

def z583 : W := mkw 0x0002000090040241 0x0000400012008048 0x000e000780040061 0x0001c000f000800c

def z584 : W := mkw 0x1000004809b81486 0x0200000901370290 0x0800000001f80000 0x01000000003f0000

def z585 : W := mkw 0x03090c0246020910 0x8061218048c04122 0x070000000e000000 0x00e0000001c00000

def z586 : W := mkw 0x000040c401009020 0x0000081880201204 0x000001c400001062 0x000000388000020c

def z587 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x8830f1c4011df067 0x91061e388023be0c

def z588 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67fef9fb80000000 0xacffdf3f70000000

def z589 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x5fce00001fffe004 0x2bf9c00003fffc00

def z590 : W := mkw 0x21101f2260000000 0x042203e44c000000 0x0000060060000000 0x000000c00c000000

def z591 : W := mkw 0x0846c09590458261 0x4108d812b208b04c 0xc8cec00791e58065 0xb919d800f23cb00c

def z592 : W := mkw 0x0eefa0199cf74641 0x41ddf403339ee8c8 0xfffff83b9fffee05 0xffffff0773fffdc0

def z593 : W := mkw 0x01000c0002000900 0x0020018000400120 0x270008001e000e00 0x24e0010003c001c0

def z594 : W := mkw 0x081053dda128b6ed 0x61020a7bb42516dd 0x20000fffe0001ffa 0x040001fffc0003ff

def z595 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xb70e0e039e001f86 0x76e1c1c073c003f0

def z596 : W := mkw 0x15b05fec2bb81d86 0x02b60bfd857703b0 0xfff1fffc7ff81f87 0xfffe3fff8fff03f0

def z597 : W := mkw 0x021b53c4350eb0ac 0x20436a7886a1d615 0x9f3ff7c47f1ff1ff 0xf3e7fef88fe3fe3f

def z598 : W := mkw 0x14b0032008980086 0x0296006401130010 0x0030000000180000 0x0006000000030000

def z599 : W := mkw 0x2ffffffff7679f71 0xc5fffffffeecf3ee 0xffffffffffe79fff 0xfffffffffffcf3ff

def z600 : W := mkw 0x07ab0c02de960b51 0x80f561805bd2c16a 0xffff0e07fffe1fff 0xffffe1c0ffffc3ff

def z601 : W := mkw 0x004680001cd74000 0x0008d000039ae800 0xd8cec0001fffe005 0xbb19d80003fffc00

def z602 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001000460060079 0x000020008c00c00f

def z603 : W := mkw 0x0846c09d90658661 0x4108d813b20cb0cc 0x60cec83f90e58e61 0x2c19d907f21cb1cc

def z604 : W := mkw 0x00000002c0000251 0x800000005800004a 0x00000007e0000078 0x00000000fc00000f

def z605 : W := mkw 0x234ffc97f6060b51 0x8469ff92fec0c16a 0xb70ffe07fe061fff 0x76e1ffc0ffc0c3ff

def z606 : W := mkw 0x14f4a36809f95486 0x029e946d013f2a90 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z607 : W := mkw 0x15b00f6acbb81fd7 0x82b601ed597703fa 0xfff00ffffff81ffe 0xfffe01ffffff03ff

def z608 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x170106007e061ffc 0x42e020c00fc0c3ff

def z609 : W := mkw 0x024ff0843447e028 0x2049fe108688fc05 0x000ff0046007e079 0x0001fe008c00fc0f

def z610 : W := mkw 0x03090c02c2000b51 0x806121805840016a 0xa70f0e07e0001ffb 0x74e1e1c0fc0003ff

def z611 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x48fff00001ffe001 0x891ffe00003ffc00

def z612 : W := mkw 0x03090c02c6020b51 0x8061218058c0416a 0x37010e07ee021ffa 0x46e021c0fdc043ff

def z613 : W := mkw 0x1fffeffd9fffdfe7 0x43fffdffb3fffbfc 0xffffffff9fffffe7 0xfffffffff3fffffc

def z614 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x8800c7c4610591ff 0x910018f88c20b23f

def z615 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x68f00ff801f81f82 0x8d1e01ff003f03f0

def z616 : W := mkw 0x0010034001081084 0x0002006800210210 0x9831f7c0011ff187 0xd3063ef80023fe30

def z617 : W := mkw 0x0046c09510450000 0x0008d812a208a000 0xe8cec9ff91e58007 0xbd19d93ff23cb000

def z618 : W := mkw 0x030b0c02d4060251 0x806161805a80c04a 0xa70f0e07e006007b 0x74e1e1c0fc00c00f

def z619 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x48cec1ff81e58061 0x8919d83ff03cb00c

def z620 : W := mkw 0x06fff3843cd74000 0x00dffe70879ae800 0xdffff7c47fffe007 0xfbfffef88ffffc00

def z621 : W := mkw 0x000000000008208c 0x2000000000010411 0x10000000001a6198 0x0200000000034c33

def z622 : W := mkw 0x224ff097f4060251 0x8449fe12fe80c04a 0x000ff007e0060079 0x0001fe00fc00c00f

def z623 : W := mkw 0x17efac281ef74d02 0x02fdf58503dee9a0 0x67ce08381ee00e00 0x2cf9c10703dc01c0

def z624 : W := mkw 0x06ffa3401ddf5084 0x00dff46803bbea10 0xdffff7c01ffff187 0xfbfffef803fffe30

def z625 : W := mkw 0x17fdaf680bb81d86 0x02ffb5ed017703b0 0xfffffff81ff81f87 0xffffffff03ff03f0

def z626 : W := mkw 0x030b0c02d0040241 0x006161805a008048 0xa70f0e07f0041e67 0x74e1e1c0fe0083cc

def z627 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x370e08039e061ffc 0x26e1c10073c0c3ff

def z628 : W := mkw 0x0010130020000000 0x0002026004000000 0x0031360060000000 0x400626c00c000000

def z629 : W := mkw 0x07ab2c02de964b51 0x80f565805bd2c96a 0xb73f3e07fe1e7fff 0x76e7e7c0ffc3cfff

def z630 : W := mkw 0x27b93f2260000000 0x04f727e44c000000 0xe7f13ff860000002 0xfcfe27ff0c000000

def z631 : W := mkw 0x27b97fa660000000 0x04f72ff4cc000000 0x8731f7c460000003 0xd0e63ef88c000000

def z632 : W := mkw 0x0000000082000b51 0x800000001040016a 0x0000000000001ff8 0x00000000000003ff

def z633 : W := mkw 0x0846801990650641 0x4108d003320ca0c8 0xe8cec83b91e58e05 0xbd19d907723cb1c0

def z634 : W := mkw 0x03195f8660000000 0x00632bf0cc000000 0xa73fffc7e0000003 0xf4e7fff8fc000000

def z635 : W := mkw 0x27b97fb760000000 0x04f72ff6ec000000 0x27313fffe0000002 0x44e627fffc000000

def z636 : W := mkw 0x030b0c0256060910 0x806161804ac0c122 0x970f06007e06019d 0x72e1e0c00fc0c033

def z637 : W := mkw 0x0846805991659661 0x4108d00b322cb2cc 0x68ce083b91e59e64 0x2d19c107723cb3cc

def z638 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x48c0c1f811e59e64 0x8918183f023cb3cc

def z639 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x8031f7c4600011fb 0xd0063ef88c00023f

def z640 : W := mkw 0x020b0002d4060251 0x804160005a80c04a 0x900f0607e00611ff 0x5201e0c0fc00c23f

def z641 : W := mkw 0x0b4fccdfd7679f71 0xc169f99bfaecf3ee 0xefcec9ff9fe59e67 0xbdf9d93ff3fcb3cc

def z642 : W := mkw 0x0002000090040241 0x0000400012008048 0xb00f0e07f0061fff 0x7601e1c0fe00c3ff

def z643 : W := mkw 0x27a92c2240000000 0x04f5258448000000 0x0700000000000000 0x00e0000000000000

def z644 : W := mkw 0x031b1f02f60e2bdd 0xa06363e05ec1c57b 0xb73f3e07fe1e7fff 0x76e7e7c0ffc3cfff

def z645 : W := mkw 0x1df4cffd0bf99da6 0x43be99ffa17f33b4 0xfff0cff81ff99f86 0xfffe19ff03ff33f0

def z646 : W := mkw 0x15b05fec2bb8bdae 0x22b60bfd857717b5 0xfff00ffc7ff81ffe 0xfffe01ff8fff03ff

def z647 : W := mkw 0x06a920000c924000 0x00d5240001924800 0x070000000e000000 0x00e0000001c00000

def z648 : W := mkw 0x03090c0240000000 0x0061218048000000 0xb70f0e07e00611ff 0x76e1e1c0fc00c23f

def z649 : W := mkw 0x35f4fffd2bb81d86 0x06be9fffa57703b0 0xfff0fff81ff81f86 0xfffe1fff03ff03f0

def z650 : W := mkw 0x11100f680bb81d86 0x022201ed017703b0 0x38000ff81ff81f86 0x070001ff03ff03f0

def z651 : W := mkw 0x100000000a980986 0x0200000001530130 0x100000000e180180 0x0200000001c30030

def z652 : W := mkw 0x1000004803281d86 0x02000009006503b0 0x0000000000001f80 0x00000000000003f0

def z653 : W := mkw 0x000050842000a028 0x20000a1084001405 0x0000000460000078 0x000000008c00000f

def z654 : W := mkw 0x0044801100000000 0x0008900220000000 0x60ce083b80000000 0x2c19c10770000000

def z655 : W := mkw 0x0846804891659661 0x4108d009122cb2cc 0xc8cec00011e59e65 0xb919d800023cb3cc

def z656 : W := mkw 0x0002000090040241 0x0000400012008048 0x200e080390000e00 0x2401c100720001c0

def z657 : W := mkw 0x0856d3ddb1659661 0x410ada7bb62cb2cc 0xe8fffffff1e59e67 0xfd1ffffffe3cb3cc

def z658 : W := mkw 0x1cf4c3fd09f994a6 0x439e987fa13f3294 0x48f0c1f801f98000 0x891e183f003f3000

def z659 : W := mkw 0x15b00f280ab80d86 0x02b601e5015701b0 0x77f00e381ef80f80 0x6efe01c703df01f0

def z660 : W := mkw 0x15a00c200a900902 0x02b4018401520120 0x070000000e000000 0x00e0000001c00000

def z661 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x5ff007f80ff80180 0xcbfe00ff01ff0030

def z662 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x9830f7c00119f186 0xd3061ef800233e30

def z663 : W := mkw 0x06efa0401ddff0ac 0x20ddf40803bbfe15 0xdffff0001ffff1fd 0xfbfffe0003fffe3f

def z664 : W := mkw 0x0eefe0dd91659661 0x41ddfc1bb22cb2cc 0xeffff9ff91e59e67 0xfdffff3ff23cb3cc

def z665 : W := mkw 0x16efa0481fff5d86 0x02ddf40903ffebb0 0xdffff0001fffff85 0xfbfffe0003fffff0

def z666 : W := mkw 0x03191f02660a299c 0xa06323e04cc14533 0x173136006e1a6198 0x42e626c00dc34c33

def z667 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x40ce000010e00000 0x2819c000021c0000

def z668 : W := mkw 0x0000000800200400 0x0000000100040080 0x60c0083810e00e00 0x2c180107021c01c0

def z669 : W := mkw 0x1010036801281486 0x0202006d00250290 0x000001f800000000 0x0000003f00000000

def z670 : W := mkw 0x04a0000008900000 0x0094000001120000 0x173000000e180000 0x42e6000001c30000

def z671 : W := mkw 0x15b00f200a980986 0x02b601e401530130 0xdff006001ff80184 0xfbfe00c003ff0030

def z672 : W := mkw 0x15b20f681fff5d86 0x02b641ed03ffebb0 0xfff00ff81fffff86 0xfffe01ff03fffff0

def z673 : W := mkw 0x0000004801201400 0x0000000900240280 0x48c001f801e00000 0x8918003f003c0000

def z674 : W := mkw 0x37ffffffffbe1fd7 0x86fffffffff7c3fa 0xfffffffffffe1fff 0xffffffffffffc3ff

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x1001060060020198 0x420020c00c004033

def z676 : W := mkw 0x15b04fec0bb89da6 0x02b609fd817713b4 0xfff0cffc1ffd9fe7 0xfffe19ff83ffb3fc

def z677 : W := mkw 0x001013002008208c 0x2002026004010411 0x9831f600611fe19d 0xd3063ec00c23fc33

def z678 : W := mkw 0x06efa00010450000 0x00ddf4000208a000 0xcffff00011e58005 0xf9fffe00023cb000

def z679 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x080ec00791e59e65 0x0101d800f23cb3cc

def z680 : W := mkw 0x05b00f6001081084 0x00b601ec00210210 0xfff00ff801181186 0xfffe01ff00230230

def z681 : W := mkw 0x000050c42108b0ac 0x20000a1884211615 0x1801f004611ff1fd 0x03003e008c23fe3f

def z682 : W := mkw 0x0046800010450000 0x0008d0000208a000 0x000ec00000058001 0x0001d8000000b000

def z683 : W := mkw 0x2a4ff0dff1659661 0x4549fe1bfe2cb2cc 0xe8cff9fff1e59e67 0xbd19ff3ffe3cb3cc

def z684 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xcfcec0001fe58005 0xb9f9d80003fcb000

def z685 : W := mkw 0x06a920000c924000 0x00d5240001924800 0xdff130001ffa6004 0xfbfe260003ff4c00

def z686 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xa70f0e07fe000e03 0x74e1e1c0ffc001c0

def z687 : W := mkw 0x0efff3ddbdfff6ed 0x61dffe7bb7bffedd 0xffffffffffffffff 0xffffffffffffffff

def z688 : W := mkw 0x04a0200008904000 0x0094040001120800 0x0030300000186000 0x0006060000030c00

def z689 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x37300ff80e181f82 0x46e601ff01c303f0

def z690 : W := mkw 0x01020c02d2040b51 0x802041805a40816a 0xa00e0e07f0041fff 0x3401c1c0fe0083ff

def z691 : W := mkw 0x27efac33d6060b51 0x84fdf5867ac0c16a 0x67ce083b9e000e00 0x2cf9c10773c001c0

def z692 : W := mkw 0x000000000c924000 0x0000000001924800 0x100000000e1a6000 0x0200000001c34c00

def z693 : W := mkw 0x15b00f200a980986 0x02b601e401530130 0xb7300e001e181f86 0x76e601c003c303f0

def z694 : W := mkw 0x0856d3ddb16db6ed 0x610ada7bb62db6dd 0xe8cecffff1e59fff 0xbd19d9fffe3cb3ff

def z695 : W := mkw 0x06eda00000000000 0x00ddb40000000000 0x47ce000000000000 0x28f9c00000000000

def z696 : W := mkw 0x15b00f600b981986 0x02b601ec01730330 0x9f3007c00f181186 0xd3e600f801e30230

def z697 : W := mkw 0x000200001cd74000 0x00004000039ae800 0x9831f0001fffe005 0xd3063e0003fffc00

def z698 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x0001f7c46007f1fb 0x00003ef88c00fe3f

def z699 : W := mkw 0x21105ff76108b0ac 0x24220bfeec211615 0x20000fffe00011fa 0x040001fffc00023f

def z700 : W := mkw 0x0eefe0959cd7c261 0x41ddfc12b39af84c 0xdffff0079fffe065 0xfbfffe00f3fffc0c

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000604600011fa 0x000000c08c00023f

def z702 : W := mkw 0x17bb0f6adfbe1fd7 0x82f761ed5bf7c3fa 0xfffe0ffb9ff81f86 0xffffc1ff73ff03f0

def z703 : W := mkw 0x01000c0242000910 0x8020018048400122 0x0000060060000198 0x000000c00c000033

def z704 : W := mkw 0x0000508420000000 0x00000a1084000000 0x0001f00460000001 0x00003e008c000000

def z705 : W := mkw 0x001003400108b0ac 0x2002006800211615 0x983007c0011ff1fe 0xd30600f80023fe3f

def z706 : W := mkw 0x04e6800018d50000 0x009cd000031aa000 0xdffec0001ffd8005 0xfbffd80003ffb000

def z707 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67fff9ffe0000001 0xacffff3ffc000000

def z708 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cfc9fff1e79e7f 0xbd19f93ffe3cf3cf

def z709 : W := mkw 0x0044c09500000000 0x00089812a0000000 0x60ce09ff80000002 0x2c19c13ff0000000

def z710 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x7fc00ff81ff81f86 0x2ff801ff03ff03f0

def z711 : W := mkw 0x27efac33ded74b51 0x84fdf5867bdae96a 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z712 : W := mkw 0x06fff3c43ddff0ac 0x20dffe7887bbfe15 0x47ce07c47ee011fa 0x28f9c0f88fdc023f

def z713 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x60ce09fb90e00e00 0x2c19c13f721c01c0

def z714 : W := mkw 0x21125fb77cd74000 0x04224bf6ef9ae800 0x38000fffffffe006 0x070001fffffffc00

def z715 : W := mkw 0x135faf68176f5d86 0x026bf5ed02edebb0 0x200ffff80007ff83 0x0401ffff0000fff0

def z716 : W := mkw 0x09105fdfe328bffd 0xe1220bfbfc6517ff 0x20000fffe0001ffa 0x040001fffc0003ff

def z717 : W := mkw 0x11000c480bb81d86 0x02200189017703b0 0xffc00ff81ff81f86 0xfff801ff03ff03f0

def z718 : W := mkw 0x14a000480bb81d86 0x02940009017703b0 0xfff009f81ff81f86 0xfffe013f03ff03f0

def z719 : W := mkw 0x03090c02c6020b51 0x8061218058c0416a 0xb70f0e07ee021ffb 0x76e1e1c0fdc043ff

def z720 : W := mkw 0x17efac2adef74f53 0x82fdf5855bdee9ea 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z721 : W := mkw 0x2144ccb740000000 0x04289996e8000000 0xe0cec9ff80000003 0xbc19d93ff0000000

def z722 : W := mkw 0x15b01f682bb8bdae 0x22b603ed057717b5 0xfff13ff87ffffffe 0xfffe27ff0fffffff

def z723 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xf7c00ff81ee01f86 0x7ef801ff03dc03f0

def z724 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7ffffffe006007b 0xfcfffffffc00c00f

def z725 : W := mkw 0x235dffb760000000 0x046bbff6ec000000 0x200e0fffe0000002 0x0401c1fffc000000

def z726 : W := mkw 0x0000409500000000 0x00000812a0000000 0xa00e09ff80000003 0x3401c13ff0000000

def z727 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff10ff87ffa1f9e 0xfffe21ff0fff43f3

def z728 : W := mkw 0x235dffb760000000 0x046bbff6ec000000 0xa03fffffe0000003 0xd407fffffc000000

def z729 : W := mkw 0x0046804891651641 0x0008d009122ca2c8 0xe8cec9ff91e59e67 0xbd19d93ff23cb3cc

def z730 : W := mkw 0x06efa0025cd74010 0x80ddf4004b9ae802 0xdffff0007fffe01d 0xfbfffe000ffffc03

def z731 : W := mkw 0x17bb0f6adfbe1fd7 0x82f761ed5bf7c3fa 0x1f3106007ffe1ffc 0x43e620c00fffc3ff

def z732 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8cfc9ff91e79e67 0xff19f93ff23cf3cc

def z733 : W := mkw 0x27edac734108b0ac 0x24fdb58e68211615 0x7fce083b811ff1fc 0x2ff9c1077023fe3f

def z734 : W := mkw 0x25f4ffb760000000 0x04be9ff6ec000000 0xe0feffffe0000003 0xbc1fdffffc000000

def z735 : W := mkw 0x034dcc9746020910 0x8069b992e8c04122 0xf7cfcfffee02019b 0xfef9f9fffdc04033

def z736 : W := mkw 0x324df0df6bb81d86 0x0649be1bed7703b0 0x180ff007fff81f85 0x0301fe00ffff03f0

def z737 : W := mkw 0x031b5fc6f70ebbfd 0xa0636bf8dee1d77f 0x2f3ef9c39f19ee00 0xa5e7df3873e33dc0

def z738 : W := mkw 0x27fdffb768900000 0x04ffbff6ed120000 0xe7fffffffee00003 0xfcffffffffdc0000

def z739 : W := mkw 0x07fdefb500000000 0x00ffbdf6a0000000 0xe7ffffff80000003 0xfcfffffff0000000

def z740 : W := mkw 0x03190f2240000000 0x006321e448000000 0xa70f0fffe0000003 0x74e1e1fffc000000

def z741 : W := mkw 0x15a00c280ab00d02 0x02b40185015601a0 0xe7c009f81ee00e02 0xbcf8013f03dc01c0

def z742 : W := mkw 0x0002004891241641 0x00004009122482c8 0x0800000011e41e64 0x01000000023c83cc

def z743 : W := mkw 0x27fdffb760002008 0x24ffbff6ec000401 0xe7ffffffe002601b 0xfcfffffffc004c03

def z744 : W := mkw 0x080200489165b669 0x61004009122cb6cd 0x0800000011e7fe7c 0x01000000023cffcf

def z745 : W := mkw 0x180200489fff9ff7 0xc300400913fff3fe 0x180000001fff9ffc 0x0300000003fff3ff

def z746 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x4ffff0001fffe001 0xa9fffe0003fffc00

def z747 : W := mkw 0x24f4f3b520000000 0x049e9e76a4000000 0x60fef9fb80000000 0xac1fdf3f70000000

def z748 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xf7ffffffe0060007 0xfefffffffc00c000

def z749 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff13ff81ffa7f86 0xfffe27ff03ff4ff0

def z750 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xb73ffe07fe061fff 0xf6e7ffc0ffc0c3ff

def z751 : W := mkw 0x001053cc2128b4ac 0x20020a7984251695 0x9831f7c471ffffff 0xd3063ef88e3fffff

def z752 : W := mkw 0x27fdffb760410000 0x04ffbff6ec082000 0xefffffffe1e18003 0xfdfffffffc3c3000

def z753 : W := mkw 0x04e4e09500000000 0x009c9c12a0000000 0xe0fef9ff80000003 0xbc1fdf3ff0000000

def z754 : W := mkw 0x15a00c680bb01d02 0x02b4018d017603a0 0x67c009f81ee01e02 0x2cf8013f03dc03c0

def z755 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8fff9ff91e59e67 0xfd1fff3ff23cb3cc

def z756 : W := mkw 0x15b00f280ab80d86 0x02b601e5015701b0 0xf7f00ff81ef80f82 0xfefe01ff03df01f0

def z757 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x1831f604611ff1fd 0x43063ec08c23fe3f

def z758 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x68ce09ff91e59e66 0x2d19c13ff23cb3cc

def z759 : W := mkw 0x0846c09d90650641 0x4108d813b20ca0c8 0x60cec9fb90e00e00 0xac19d93f721c01c0

def z760 : W := mkw 0x2154dfb760000000 0x042a9bf6ec000000 0x60ce0fffe0000002 0x2c19c1fffc000000

def z761 : W := mkw 0x0144cc9500000000 0x00289992a0000000 0xe7cecfff80000003 0xfcf9d9fff0000000

def z762 : W := mkw 0x17b90f224e9a0996 0x82f721e449d34132 0xf7ff0fffee1a019b 0xfeffe1fffdc34033

def z763 : W := mkw 0x0ea960dd8db2d661 0x41d52c1bb1b65acc 0x373139ff8e1a7e62 0x46e6273ff1c34fcc

def z764 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x7ff009f81ff81f84 0xaffe013f03ff03f0

def z765 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xcffff0001ff9e001 0xf9fffe0003ff3c00

def z766 : W := mkw 0x15a05cac2ab0ad2a 0x22b40b95855615a5 0x67c1f83c7ee7ee79 0x2cf83f078fdcfdcf

def z767 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xfffff9f81fffe007 0xffffff3f03fffc00

def z768 : W := mkw 0x27fdffb760414000 0x04ffbff6ec082800 0xe7ffffffe001e003 0xfcfffffffc003c00

def z769 : W := mkw 0x1802004899fd96e7 0x43004009133fb2dc 0x0800000011fd9e64 0x01000000023fb3cc

def z770 : W := mkw 0x06efa002dcd74251 0x80ddf4005b9ae84a 0xdffff607fffff1ff 0xfbfffec0fffffe3f

def z771 : W := mkw 0x14b003680bb81d86 0x0296006d017703b0 0xdff001f81ff81f84 0xfbfe003f03ff03f0

def z772 : W := mkw 0x0846d0ddb165b669 0x6108da1bb62cb6cd 0xf8fff9fff1fffe7f 0xff1fff3ffe3fffcf

def z773 : W := mkw 0x26fdf3b760000000 0x04dfbe76ec000000 0x40fef1fb80000000 0x881fde3f70000000

def z774 : W := mkw 0x27fdffb768d14000 0x04ffbff6ed1a2800 0xffffffffe1ffe007 0xfffffffffc3ffc00

def z775 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xb73f3e07fe1e7fff 0x76e7e7c0ffc3cfff

def z776 : W := mkw 0x0846805991651641 0x4108d00b322ca2c8 0xe8cec9fb91e59e07 0xbd19d93f723cb3c0

def z777 : W := mkw 0x080240dd91249661 0x4100481bb22492cc 0xe8ce09ff91e41e67 0xbd19c13ff23c83cc

def z778 : W := mkw 0x06efa0009cd74241 0x00ddf400139ae848 0xdffff0079fffe065 0xfbfffe00f3fffc0c

def z779 : W := mkw 0x224de09740000000 0x0449bc12e8000000 0xe0cec9ff80000003 0xbc19d93ff0000000

def z780 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8cec9ff91e79fff 0xbf19d93ff23cf3ff

def z781 : W := mkw 0x024f800014470000 0x0049f0000288e000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z782 : W := mkw 0x2fbb3f6af1659661 0x45f767ed5e2cb2cc 0x0f31360071e59e64 0x41e626c00e3cb3cc

def z783 : W := mkw 0x000240cc91249661 0x00004819922492cc 0xe8cec9ff91e59e67 0xbd19d93ff23cb3cc

def z784 : W := mkw 0x15b01f682bb81d86 0x02b603ed057703b0 0xfff13ff87ff81f86 0xfffe27ff0fff03f0

def z785 : W := mkw 0x0000004801201400 0x0000000900240280 0xe8ce09ff91e01e07 0xbd19c13ff23c03c0

def z786 : W := mkw 0x0802004891651641 0x41004009122ca2c8 0x0800000011e01e04 0x01000000023c03c0

def z787 : W := mkw 0x27fdffb764024000 0x04ffbff6ec804800 0xe7ffffffe0026003 0xfcfffffffc004c00

def z788 : W := mkw 0x0ca2004899f59661 0x41944009133eb2cc 0xdff000001ffd9e64 0xfbfe000003ffb3cc

def z789 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff0041ffff067 0xfbfffe0083fffe0c

def z790 : W := mkw 0x1cf4d3fd29f9b4ae 0x639e9a7fa53f3695 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z791 : W := mkw 0x11105feee328bfff 0xa2220bfddc6517ff 0x20000fffe0001ffa 0x040001fffc0003ff

def z792 : W := mkw 0x27fdaf3340000000 0x04ffb5e668000000 0xe7ff0fffe0000003 0xfcffe1fffc000000

def z793 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67ce09fb80000000 0x2cf9c13f70000000

def z794 : W := mkw 0x0846c0dd916db6ed 0x6108d81bb22db6dd 0xe8cec9ff91e59fff 0xbd19d93ff23cb3ff

def z795 : W := mkw 0x06ab20001cd74000 0x00d56400039ae800 0x9f31f0001fffe005 0xd3e63e0003fffc00

def z796 : W := mkw 0x0846c0dd95679661 0x4108d81bb2acf2cc 0xf8cec9ff9fe79e67 0xbf19d93ff3fcf3cc

def z797 : W := mkw 0x0046c09590450241 0x0008d812b208a048 0xe8cec9ff91e59e67 0xbd19d93ff23cb3cc

def z798 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xffcf0e07ffe61fff 0xfff9e1c0fffcc3ff

def z799 : W := mkw 0x06efa002dcd74251 0x80ddf4005b9ae84a 0xfffff807fffffe7f 0xffffff00ffffffcf

def z800 : W := mkw 0x020b00001cd74000 0x00416000039ae800 0x9f3ff0001fffe005 0xf3e7fe0003fffc00

def z801 : W := mkw 0x16bb036addbe16d7 0x82d7606d5bb7c2da 0x48ff01ffe1fe0079 0x891fe03ffc3fc00f

def z802 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff6047fffe007 0xfbfffec08ffffc00

def z803 : W := mkw 0x27fdffb76c9a608c 0x24ffbff6ed934c11 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z804 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x9f31f7c47f1ff1ff 0xf3e63ef88fe3fe3f

def z805 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xf7fffffffe000007 0xfeffffffffc00000

def z806 : W := mkw 0x0b4dccdf47639d30 0xc169b99be8ec73a6 0x5fc1c7f86fe38198 0xcbf838ff0dfc7033

def z807 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0xc8c0000011e59e64 0xb9180000023cb3cc

def z808 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x170f0607fe061ffd 0x42e1e0c0ffc0c3ff

def z809 : W := mkw 0x15f4cfb50a980986 0x02be99f6a1530130 0xf7fecfff8e180183 0xfeffd9fff1c30030

def z810 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xe0cfcfffe0000003 0xfc19f9fffc000000

def z811 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x1831f7c4611fe1f9 0xc3063ef88c23fc3f

def z812 : W := mkw 0x0054d39520000000 0x000a9a72a4000000 0xe0fef9ff80000003 0xbc1fdf3ff0000000

def z813 : W := mkw 0x27fdffb76c924000 0x04ffbff6ed924800 0xe7ffffffee000003 0xfcfffffffdc00000

def z814 : W := mkw 0x05e4ac02cad14b51 0x80bc9580595a296a 0x68f0fe07e1f9fffa 0x8d1e1fc0fc3f3fff

def z815 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfffe0fff9ff81f87 0xffffc1fff3ff03f0

def z816 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff1fff81ff81f87 0xfffe3fff03ff03f0

def z817 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe0cec9ff90e01e63 0xbc19d93ff21c03cc

def z818 : W := mkw 0x0a4fe0959447c261 0x4149fc12b288f84c 0x000ec00780058061 0x0001d800f000b00c

def z819 : W := mkw 0x0044801100000000 0x0008900220000000 0xe0ce09fb80000002 0xbc19c13f70000000

def z820 : W := mkw 0x0a4fc09594478261 0x4149f812b288f04c 0x000fc00780078061 0x0001f800f000f00c

def z821 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x8800c00011e59e65 0x91001800023cb3cc

def z822 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x47fff7ffe0000001 0xc8fffefffc000000

def z823 : W := mkw 0x0002004891241641 0x00004009122482c8 0xe8ce09fb91e01e06 0xbd19c13f723c03c0

def z824 : W := mkw 0x080200489df7d661 0x4100400913befacc 0x080000001fe59e64 0x0100000003fcb3cc

def z825 : W := mkw 0x0846c0dd95679671 0xc108d81bb2acf2ce 0xe8cec9ff91e79e7f 0xbd19d93ff23cf3cf

def z826 : W := mkw 0x08020048916db6ed 0x61004009122db6dd 0x0800000011fdfe64 0x01000000023fbfcc

def z827 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x370f0e07fe021ffa 0x66e1e1c0ffc043ff

def z828 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8fec9ff91fd9e67 0xff1fd93ff23fb3cc

def z829 : W := mkw 0x27fdffb768d14000 0x04ffbff6ed1a2800 0xfffffffffff9e007 0xffffffffffff3c00

def z830 : W := mkw 0x01020c0092040b41 0x0020418012408168 0xb70f0e07fe061fff 0x76e1e1c0ffc0c3ff

def z831 : W := mkw 0x225df39760000000 0x044bbe72ec000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z832 : W := mkw 0x06efa0009cd74241 0x00ddf400139ae848 0xdffff0001ffffe65 0xfbfffe0003ffffcc

def z833 : W := mkw 0x23195fb760000000 0x04632bf6ec000000 0x270e0fffe0000002 0x24e1c1fffc000000

def z834 : W := mkw 0x27fdffb76008208c 0x24ffbff6ec010411 0xffffffffe11fe19f 0xfffffffffc23fc33

def z835 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff1fffc7fffffff 0xfffe3fff8fffffff

def z836 : W := mkw 0x19105ffda328bfef 0x63220bffb46517fd 0x20000fffe0001ffa 0x040001fffc0003ff

def z837 : W := mkw 0x15a00c680bb01d02 0x02b4018d017603a0 0x6fc009f81fe00e00 0xadf8013f03fc01c0

def z838 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x0800000011e18e00 0x01000000023c31c0

def z839 : W := mkw 0x23195fb760000000 0x04632bf6ec000000 0xa73fffffe0000003 0xf4e7fffffc000000

def z840 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xefffffffe1058007 0xfdfffffffc20b000

def z841 : W := mkw 0x06ab00001c960000 0x00d560000392c000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z842 : W := mkw 0x14b0036809b81486 0x0296006d01370290 0xfff009f81ff81e06 0xfffe013f03ff03c0

def z843 : W := mkw 0x25f4ffb520000000 0x04be9ff6a4000000 0xe7feffff80000003 0xfcffdffff0000000

def z844 : W := mkw 0x0a4ff095b447e269 0x6149fe12b688fc4d 0x000ff007e007e079 0x0001fe00fc00fc0f

def z845 : W := mkw 0x0054d39520000000 0x000a9a72a4000000 0xe0cecfffe0000003 0xbc19d9fffc000000

def z846 : W := mkw 0x27fdffb76000a028 0x24ffbff6ec001405 0xe7ffffffe000007b 0xfcfffffffc00000f

def z847 : W := mkw 0x2a4ff097f447c261 0x4549fe12fe88f84c 0x000ff007e007e061 0x0001fe00fc00fc0c

def z848 : W := mkw 0x27fdffb76c924000 0x04ffbff6ed924800 0xfffffffffffa6007 0xffffffffffff4c00

def z849 : W := mkw 0x11105fec2328bdae 0x22220bfd846517b5 0x20000ff800001f82 0x040001ff000003f0

def z850 : W := mkw 0x0044805901201400 0x0008900b20240280 0xe8ce09fb91e01e06 0xbd19c13f723c03c0

def z851 : W := mkw 0x07fdcfb740000000 0x00ffb9f6e8000000 0xe7ffcfffe0000003 0xfcfff9fffc000000

def z852 : W := mkw 0x2ffdffb760418020 0x45ffbff6ec083004 0xe7ffffffe0018003 0xfcfffffffc003000

def z853 : W := mkw 0x08020048916d96e5 0x41004009122db2dc 0x1800000011fd9fe4 0x03000000023fb3fc

def z854 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x5ff007f81ff81f84 0xcbfe00ff03ff03f0

def z855 : W := mkw 0x030b2c02d6064b51 0x806165805ac0c96a 0xb70f3e07fe067fff 0x76e1e7c0ffc0cfff

def z856 : W := mkw 0x01100f4803281d84 0x002201e9006503b0 0xfff00ff81ff81f86 0xfffe01ff03ff03f0

def z857 : W := mkw 0x37b93f226a98298e 0x26f727e44d530531 0x173136006e1a6198 0x42e626c00dc34c33

def z858 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xe8cec9ff81058007 0xbd19d93ff020b000

def z859 : W := mkw 0x05f4dfb520000000 0x00be9bf6a4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z860 : W := mkw 0x26fdf3b760000000 0x04dfbe76ec000000 0xe0fff9ffe0000003 0xbc1fff3ffc000000

def z861 : W := mkw 0x0044c09500000000 0x00089812a0000000 0x40cec1ff80000001 0x8819d83ff0000000

def z862 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xb70e0e07fe001ffe 0x76e1c1c0ffc003ff

def z863 : W := mkw 0x37fdffb762080986 0x06ffbff6ec410130 0xe7ffffffe0000183 0xfcfffffffc000030

def z864 : W := mkw 0x37b93f226a900902 0x06f727e44d520120 0x073136006e000000 0x40e626c00dc00000

def z865 : W := mkw 0x024dc09500000000 0x0049b812a0000000 0xe7cfc9ff80000003 0xfcf9f93ff0000000

def z866 : W := mkw 0x1df6cfb59add8be7 0x43bed9f6b35bb17c 0x173ec6078e1d81e1 0x42e7d8c0f1c3b03c

def z867 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff10ff81ffe1f87 0xfffe21ff03ffc3f0

def z868 : W := mkw 0x04a0004809b01400 0x0094000901360280 0xefc009f81fe01e06 0xbdf8013f03fc03c0

def z869 : W := mkw 0x27fdffb762000900 0x04ffbff6ec400120 0xf7fffffffe061fff 0xfeffffffffc0c3ff

def z870 : W := mkw 0x0000004801201400 0x0000000900240280 0xffc009f81fe01e06 0xfff8013f03fc03c0

def z871 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x67c009f81ee00e00 0x2cf8013f03dc01c0

def z872 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x60cec9ff90e59e63 0x2c19d93ff21cb3cc

def z873 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff10ffc7ff81f87 0xfffe21ff8fff03f0

def z874 : W := mkw 0x0846805991651641 0x4108d00b322ca2c8 0x68ce09fb91e00e00 0xad19c13f723c01c0

def z875 : W := mkw 0x27fdffb762000910 0x84ffbff6ec400122 0xe7ffffffe000019b 0xfcfffffffc000033

def z876 : W := mkw 0x27fdffb764020010 0x84ffbff6ec804002 0xe7ffffffe002001b 0xfcfffffffc004003

def z877 : W := mkw 0x24f6f3b5b6060b51 0x849ede76b6c0c16a 0x50f0f1f81e061ffc 0x8a1e1e3f03c0c3ff

def z878 : W := mkw 0x0846c09d90650641 0x4108d813b20ca0c8 0x60ce09ff90e00e02 0x2c19c13ff21c01c0

def z879 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0ce09ff80000003 0xbc19c13ff0000000

def z880 : W := mkw 0x0802004897269f71 0xc100400912e4d3ee 0x100000001e061ffc 0x0200000003c0c3ff

def z881 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7fffffff0001e07 0xfcfffffffe0003c0

def z882 : W := mkw 0x05b00f2000000000 0x00b601e400000000 0xe7fe0fff80000003 0xfcffc1fff0000000

def z883 : W := mkw 0x25f4dfb760000000 0x04be9bf6ec000000 0xe7fecfffe0000003 0xfcffd9fffc000000

def z884 : W := mkw 0x030b0c02d6470b51 0x806161805ac8e16a 0xbf0f0e07ffe79fff 0x77e1e1c0fffcf3ff

def z885 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xf7ffffffe0001187 0xfefffffffc000230

def z886 : W := mkw 0x17b90f224a980986 0x02f721e449530130 0x173106006e180180 0x42e620c00dc30030

def z887 : W := mkw 0x08569319b06d26cd 0x610ad263360da4d9 0x70ff3e3bf0fa6f98 0x6e1fe7c77e1f4df3

def z888 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x5ff1f0001fffe004 0xcbfe3e0003fffc00

def z889 : W := mkw 0x37b93f226e9a4986 0x06f727e44dd34930 0x173136006e1a6180 0x42e626c00dc34c30

def z890 : W := mkw 0x001053842008a0ac 0x20020a7084011415 0x9031f7c4601fe1fb 0xd2063ef88c03fc3f

def z891 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67feffffe0000002 0xacffdffffc000000

def z892 : W := mkw 0x15b00f280ab00d02 0x02b601e5015601a0 0x67c00ff81ee00e02 0x2cf801ff03dc01c0

def z893 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff0001ffff1fd 0xfbfffe0003fffe3f

def z894 : W := mkw 0x15b02f680bb85d86 0x02b605ed01770bb0 0xfff03ff81ff87f86 0xfffe07ff03ff0ff0

def z895 : W := mkw 0x15b00f680bb89da6 0x02b601ed017713b4 0xfff00ff81ffd9fe6 0xfffe01ff03ffb3fc

def z896 : W := mkw 0x0846c0dd9165b669 0x6108d81bb22cb6cd 0xe8cec9ff91e7fe7f 0xbd19d93ff23cffcf

def z897 : W := mkw 0x000040c401009020 0x0000081880201204 0x9831f7c4611ff1ff 0xd3063ef88c23fe3f

def z898 : W := mkw 0x0846c09d90658661 0x4108d813b20cb0cc 0xe0cec9ff90e58e63 0xbc19d93ff21cb1cc

def z899 : W := mkw 0x0846e0dd9165d661 0x4108dc1bb22cbacc 0xe8cef9ff91e5fe67 0xbd19df3ff23cbfcc

def z900 : W := mkw 0x0802004899f59661 0x41004009133eb2cc 0x180000001ffd9e64 0x0300000003ffb3cc

def z901 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff00ff81ffe1ffe 0xfffe01ff03ffc3ff

def z902 : W := mkw 0x07edec9740000000 0x00fdbd92e8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z903 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff6007fffe19d 0xfbfffec00ffffc33

def z904 : W := mkw 0x035ddf9760000000 0x006bbbf2ec000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z905 : W := mkw 0x2846f0ddb1659661 0x4508de1bb62cb2cc 0xe8cef9ff91e59e67 0xbd19df3ff23cb3cc

def z906 : W := mkw 0x37fdffb76a980986 0x06ffbff6ed530130 0xfffffffffff80187 0xffffffffffff0030

def z907 : W := mkw 0x09020c4893659f61 0x41204189126cb3ec 0xbf000e001fe59fe6 0x77e001c003fcb3fc

def z908 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xf7cf0ffffe061fff 0xfef9e1ffffc0c3ff

def z909 : W := mkw 0x26efa0135cd74000 0x04ddf4026b9ae800 0xdffff0039fffe005 0xfbfffe0073fffc00

def z910 : W := mkw 0x27fdffb76cd34000 0x04ffbff6ed9a6800 0xffffffffeffbe003 0xfffffffffdff7c00

def z911 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff00ffc7ff81ffe 0xfffe01ff8fff03ff

def z912 : W := mkw 0x37fdffb76a98298e 0x26ffbff6ed530531 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z913 : W := mkw 0x15b00f680bb8bdae 0x22b601ed017717b5 0xfff1fff81fffffff 0xfffe3fff03ffffff

def z914 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xeff009f81ff81e06 0xbdfe013f03ff03c0

def z915 : W := mkw 0x0044d09520000000 0x00089a12a4000000 0xe0cff9ffe0000003 0xbc19ff3ffc000000

def z916 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0xb83fffc7e11ff1ff 0xf707fff8fc23fe3f

def z917 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cec9fb91e19e06 0xbd19d93f723c33c0

def z918 : W := mkw 0x0846d0ddb1659661 0x4108da1bb62cb2cc 0xe8cff9fff1e59e67 0xbd19ff3ffe3cb3cc

def z919 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff0fff81ff9ff86 0xfffe1fff03ff3ff0

def z920 : W := mkw 0x27fdffb768900000 0x04ffbff6ed120000 0xffffffffffffe007 0xfffffffffffffc00

def z921 : W := mkw 0x04a200001cd74000 0x00944000039ae800 0xdff1f0001fffe005 0xfbfe3e0003fffc00

def z922 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x273fffffe0000003 0x44e7fffffc000000

def z923 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xa70f0e07fe001ffb 0x74e1e1c0ffc003ff

def z924 : W := mkw 0x0044c09d00200400 0x00089813a0040080 0xe0cec9ff90e00e03 0xbc19d93ff21c01c0

def z925 : W := mkw 0x2a4ff097f4478271 0xc549fe12fe88f04e 0x000ff007e0078079 0x0001fe00fc00f00f

def z926 : W := mkw 0x0846c0dd916db6ed 0x6108d81bb22db6dd 0xf8fff9ff91ffffff 0xff1fff3ff23fffff

def z927 : W := mkw 0x27b93f226e924910 0x84f727e44dd24922 0x173136006e1a6198 0x42e626c00dc34c33

def z928 : W := mkw 0x27fdffb76c924000 0x04ffbff6ed924800 0xffffffffef1fe007 0xfffffffffde3fc00

def z929 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67fffffbe0000000 0xecffffff7c000000

def z930 : W := mkw 0x15a00c680bb01d02 0x02b4018d017603a0 0xfff009f81ff81e06 0xfffe013f03ff03c0

def z931 : W := mkw 0x0846c0dd91651641 0x4108d81bb22ca2c8 0xe8cec9ff91e01e07 0xbd19d93ff23c03c0

def z932 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xbf0fce07ff079fff 0xf7e1f9c0ffe0f3ff

def z933 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x370e0e07fe061ffe 0x26e1c1c0ffc0c3ff

def z934 : W := mkw 0x080200489ff7df71 0xc100400913fefbee 0x180000001ffffffc 0x0300000003ffffff

def z935 : W := mkw 0x100200489fbebfff 0xa200400913f7d7ff 0x180000001ffffffc 0x0300000003ffffff

def z936 : W := mkw 0x04e4a00008d14000 0x009c9400011a2800 0xdff1f0001fffe005 0xfbfe3e0003fffc00

def z937 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x9831f00011fffe65 0xd3063e00023fffcc

def z938 : W := mkw 0x030b0c02d6474b51 0x806161805ac8e96a 0xb70f0e07fe07ffff 0x76e1e1c0ffc0ffff

def z939 : W := mkw 0x0846d0ddb16db6ed 0x6108da1bb62db6dd 0xf8cff9fff1ffffff 0xbf19ff3ffe3fffff

def z940 : W := mkw 0x06efa002dcd74251 0x80ddf4005b9ae84a 0xdffff0039fffe005 0xfbfffe0073fffc00

def z941 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x1800000011fffe64 0x03000000023fffcc

def z942 : W := mkw 0x0144cc9740000000 0x00289992e8000000 0xe0cecfffe0000003 0xbc19d9fffc000000

def z943 : W := mkw 0x26fdf3b520000000 0x04dfbe76a4000000 0xe7fff9ff80000003 0xfcffff3ff0000000

def z944 : W := mkw 0x001053842008a0ac 0x20020a7084011415 0x9031f604601ff1ff 0x52063ec08c03fe3f

def z945 : W := mkw 0x0a4fe097d447c271 0xc149fc12fa88f84e 0x000ff007e007e079 0x0001fe00fc00fc0f

def z946 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe0ce09ff90e41e67 0x3c19c13ff21c83cc

def z947 : W := mkw 0x26fdf3b760000000 0x04dfbe76ec000000 0xc0fff7ffe0000003 0xd81ffefffc000000

def z948 : W := mkw 0x0044c09500000000 0x00089812a0000000 0x60cec9fb80000000 0xac19d93f70000000

def z949 : W := mkw 0x27b93f2260000000 0x04f727e44c000000 0xe7ff3fffe0000003 0xfcffe7fffc000000

def z950 : W := mkw 0x15b00f280ab00d02 0x02b601e5015601a0 0xf7f00ff81ee01f86 0xfefe01ff03dc03f0

def z951 : W := mkw 0x27fdffb76000a028 0x24ffbff6ec001405 0xf7ffffffe007f1ff 0xfefffffffc00fe3f

def z952 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xfffff8079fffe007 0xffffff00f3fffc00

def z953 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x6ff00ff81ff81f82 0xadfe01ff03ff03f0

def z954 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7ffffffe007e003 0xfcfffffffc00fc00

def z955 : W := mkw 0x0846805991651641 0x4108d00b322ca2c8 0xe8ce09ff91e41e67 0xbd19c13ff23c83cc

def z956 : W := mkw 0x06efa0009cd74241 0x00ddf400139ae848 0xfffffe07ffffffff 0xffffffc0ffffffff

def z957 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xffffffffe11ff1ff 0xfffffffffc23fe3f

def z958 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0xf8f1fffc611ff1ff 0xff1e3fff8c23fe3f

def z959 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cfcffff1e59e67 0xfd19f9fffe3cb3cc

def z960 : W := mkw 0x0eab20489df7d661 0x41d5640913befacc 0x1f3130001ffffe64 0x43e6260003ffffcc

def z961 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7cf0fffe0000003 0x7cf9e1fffc000000

def z962 : W := mkw 0x15b00f680bb83d8e 0x22b601ed017707b1 0xfff00ff81ffa7f9e 0xfffe01ff03ff4ff3

def z963 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x1f3ff0001fffe005 0x43e7fe0003fffc00

def z964 : W := mkw 0x17b92f224e9a4996 0x82f725e449d34932 0x173136006e1a6198 0x42e626c00dc34c33

def z965 : W := mkw 0x27fdffb762000900 0x04ffbff6ec400120 0xe7fffffffe000e03 0xfcffffffffc001c0

def z966 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff00ff81fffff86 0xfffe01ff03fffff0

def z967 : W := mkw 0x26fdf3b760000000 0x04dfbe76ec000000 0xc7fff1ffe0000001 0xf8fffe3ffc000000

def z968 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xe7f00ff81ee01f82 0xfcfe01ff03dc03f0

def z969 : W := mkw 0x27fdffb764020000 0x04ffbff6ec804000 0xf7ffffffee020003 0xfefffffffdc04000

def z970 : W := mkw 0x27fdffb762000900 0x04ffbff6ec400120 0xf7ffffffee000183 0xfefffffffdc00030

def z971 : W := mkw 0x37b93f226e9a0996 0x86f727e44dd34132 0x173136006e1a0198 0x42e626c00dc34033

def z972 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7fefffb80000002 0xfcffdfff70000000

def z973 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z974 : W := mkw 0x27fdffb768900000 0x04ffbff6ed120000 0xefffffffe1f80003 0xfdfffffffc3f0000

def z975 : W := mkw 0x15b00f680bb8bdae 0x22b601ed017717b5 0xfff10ffc7fffffff 0xfffe21ff8fffffff

def z976 : W := mkw 0x06efa0111cd74000 0x00ddf402239ae800 0xfffff83b9fffe005 0xffffff0773fffc00

def z977 : W := mkw 0x100200489fbe1fd7 0x8200400913f7c3fa 0x180000001ff81f84 0x0300000003ff03f0

def z978 : W := mkw 0x05b00f200a900900 0x00b601e401520120 0xfff00ff81ff81f86 0xfffe01ff03ff03f0

def z979 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff6001ffff187 0xfbfffec003fffe30

def z980 : W := mkw 0x080200489dfff6ed 0x6100400913bffedd 0x180000001ffffffc 0x0300000003ffffff

def z981 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cec9ff91e18e03 0xbd19d93ff23c31c0

def z982 : W := mkw 0x26efa0311cd74000 0x04ddf406239ae800 0xdffff0381fffe005 0xfbfffe0703fffc00

def z983 : W := mkw 0x27fdffb76008208c 0x24ffbff6ec010411 0xf7ffffffe01e71ff 0xfefffffffc03ce3f

def z984 : W := mkw 0x04f4c3b500000000 0x009e9876a0000000 0xe0fec9ff80000003 0xbc1fd93ff0000000

def z985 : W := mkw 0x04e4a00008d14000 0x009c9400011a2800 0x5ff0f0000ff9e000 0xcbfe1e0001ff3c00

def z986 : W := mkw 0x13090c4a4bb81d86 0x02612189497703b0 0xbf0f0e07fff81f87 0x77e1e1c0ffff03f0

def z987 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xe8cec9ff91e00007 0xbd19d93ff23c0000

def z988 : W := mkw 0x2154dfb760000000 0x042a9bf6ec000000 0x200ecfffe0000003 0x0401d9fffc000000

def z989 : W := mkw 0x0044d0952000a028 0x20089a12a4001405 0xe0cff9ffe007e07b 0xbc19ff3ffc00fc0f

def z990 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7ffffffe0041067 0xfcfffffffc00820c

def z991 : W := mkw 0x27fdffb768904000 0x04ffbff6ed120800 0xe7ffffffe0186003 0xfcfffffffc030c00

def z992 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0xa800080011e59e66 0x35000100023cb3cc

def z993 : W := mkw 0x0846c0dd916d96e5 0x4108d81bb22db2dc 0xf8cec9ff91fd9fe7 0xbf19d93ff23fb3fc

def z994 : W := mkw 0x0010538420000000 0x00020a7084000000 0x9831f7c4611ff1ff 0xd3063ef88c23fe3f

def z995 : W := mkw 0x06efa0009cd74241 0x00ddf400139ae848 0xfffff8039fffee05 0xffffff0073fffdc0

def z996 : W := mkw 0x0b0b0c4ad7679f71 0xc16161895aecf3ee 0x1f0106007fe79ffc 0x43e020c00ffcf3ff

def z997 : W := mkw 0x06efa0009cd74251 0x80ddf400139ae84a 0xdffff0001fffe07d 0xfbfffe0003fffc0f

def z998 : W := mkw 0x0844c0dd01619420 0x4108981ba02c3284 0xe8cec9ff91e19e07 0xbd19d93ff23c33c0

def z999 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xf0cfcfffe00611ff 0xfe19f9fffc00c23f

def z1000 : W := mkw 0x0846c09d90650641 0x4108d813b20ca0c8 0xe0cec9ff90e41e67 0xbc19d93ff21c83cc

def z1001 : W := mkw 0x15b01f682bb83d8e 0x22b603ed057707b1 0xfff00ff87ff81f9e 0xfffe01ff0fff03f3

def z1002 : W := mkw 0x27fdaf3340000000 0x04ffb5e668000000 0xe7fffffb80000003 0xfcffffff70000000

def z1003 : W := mkw 0x024de09500000000 0x0049bc12a0000000 0xe0cff9ff80000003 0xbc19ff3ff0000000

def z1004 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x1800000011e79ffc 0x03000000023cf3ff

def z1005 : W := mkw 0x15b00f680bb8bdae 0x22b601ed017717b5 0xfff00ff81ff81ffe 0xfffe01ff03ff03ff

def z1006 : W := mkw 0x08121348b16db6ed 0x61024269162db6dd 0x1831360071fffffc 0x430626c00e3fffff

def z1007 : W := mkw 0x06eda00008900000 0x00ddb40001120000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z1008 : W := mkw 0x0844c0dd81619661 0x4108981bb02c32cc 0xe8cec9ff81e19e63 0xbd19d93ff03c33cc

def z1009 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7ffffffe00011fb 0xfcfffffffc00023f

def z1010 : W := mkw 0x06eda0000cd34000 0x00ddb400019a6800 0xdff1f0000fffe005 0xdbfe3e0001fffc00

def z1011 : W := mkw 0x23195fb760000000 0x04632bf6ec000000 0x200f0fffe0000003 0x0401e1fffc000000

def z1012 : W := mkw 0x080200489567d661 0x4100400912acfacc 0x0800000011e7fe64 0x01000000023cffcc

def z1013 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xfffff8001ffffe07 0xffffff0003ffffc0

def z1014 : W := mkw 0x27fdffb766020910 0x84ffbff6ecc04122 0xf7fffffffe021f9f 0xfeffffffffc043f3

def z1015 : W := mkw 0x201053f52108b0ac 0x24020a7ea4211615 0x9831f7fc611ff1ff 0xd3063eff8c23fe3f

def z1016 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cecffff1e59fff 0xbd19d9fffe3cb3ff

def z1017 : W := mkw 0x2054d3b520000000 0x040a9a76a4000000 0xe0cec9ff80000003 0xbc19d93ff0000000

def z1018 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cec9fb91e58e05 0xbd19d93f723cb1c0

def z1019 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x77f00ff81ef81f82 0x6efe01ff03df03f0

def z1020 : W := mkw 0x05b20f2096060b51 0x80b641e412c0c16a 0xf7f00ff81e061ffe 0xfefe01ff03c0c3ff

def z1021 : W := mkw 0x15b01f682bb83d8e 0x22b603ed057707b1 0xfff03ff81ff87f86 0xfffe07ff03ff0ff0

def z1022 : W := mkw 0x0054c39500000000 0x000a9872a0000000 0xe0fecfff80000003 0xfc1fd9fff0000000

def z1023 : W := mkw 0x224df09760000000 0x0449be12ec000000 0x40cff1ffe0000001 0x8819fe3ffc000000

def z1024 : W := mkw 0x27fdaf3340000000 0x04ffb5e668000000 0x67fe09fb80000000 0xacffc13f70000000

def z1025 : W := mkw 0x05b00f6803201d00 0x00b601ed006403a0 0xfff00ff81fe01f86 0xfffe01ff03fc03f0

def z1026 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xe0cec9ff90001e07 0xbc19d93ff20003c0

def z1027 : W := mkw 0x26edf09760000000 0x04ddbe12ec000000 0xe7fff9ffe0000003 0xfcffff3ffc000000

def z1028 : W := mkw 0x001053cc2128b4ac 0x20020a7984251695 0xd8f1f7fc61fff1ff 0xdb1e3eff8c3ffe3f

def z1029 : W := mkw 0x24e4e0b500000000 0x049c9c16a0000000 0xe0cec9ff80000003 0xbc19d93ff0000000

def z1030 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff0cff81ffd9f87 0xfffe19ff03ffb3f0

def z1031 : W := mkw 0x35b03f682bb81d86 0x06b607ed057703b0 0xfff03ff81ff81f86 0xfffe07ff03ff03f0

def z1032 : W := mkw 0x27edecb740000000 0x04fdbd96e8000000 0x67cec9fb80000000 0xacf9d93f70000000

def z1033 : W := mkw 0x27edac3340000000 0x04fdb58668000000 0xe7ce09fb80000002 0xbcf9c13f70000000

def z1034 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xffffffffe1180007 0xfffffffffc230000

def z1035 : W := mkw 0x01000c4803201d00 0x00200189006403a0 0xefc009f81fe01e06 0xbdf8013f03fc03c0

def z1036 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8cff9ff91e7fe67 0xbd19ff3ff23cffcc

def z1037 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x0831f7c4611ff1fb 0x81063ef88c23fe3f

def z1038 : W := mkw 0x06eda0000cd34000 0x00ddb400019a6800 0xdff1f0001ffbe004 0xfbfe3e0003ff7c00

def z1039 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x370f0e07ee061ffb 0x46e1e1c0fdc0c3ff

def z1040 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff00ffc1ffc1fe7 0xfffe01ff83ff83fc

def z1041 : W := mkw 0x020b000094060241 0x004160001280c048 0xb70f0e07fe061fff 0x76e1e1c0ffc0c3ff

def z1042 : W := mkw 0x0cf4f3dd29f9f4ac 0x619e9e7ba53f3e95 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z1043 : W := mkw 0x34f4f3fd29b8b4ae 0x269e9e7fa5371695 0x48f0f1f801f9e000 0x891e1e3f003f3c00

def z1044 : W := mkw 0x2044f09520000000 0x04089e12a4000000 0xe0cef9ff80000003 0xbc19df3ff0000000

def z1045 : W := mkw 0x27fdffb76008a0ac 0x24ffbff6ec011415 0xf7ffffffe01fe1fb 0xfefffffffc03fc3f

def z1046 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xfff009f81ff80e04 0xfffe013f03ff01c0

def z1047 : W := mkw 0x03090c0242000900 0x0061218048400120 0xb70f0e07fe061fff 0x76e1e1c0ffc0c3ff

def z1048 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xffcec9ff9fe59e67 0xfff9d93ff3fcb3cc

def z1049 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xe0cec9ff80041067 0xbc19d93ff000820c

def z1050 : W := mkw 0x0fefac1bdef74f51 0xc1fdf5837bdee9ea 0x67ce083b9ee00e00 0x2cf9c10773dc01c0

def z1051 : W := mkw 0x0010034001081084 0x0002006800210210 0x9831f7c4611ff1ff 0xd3063ef88c23fe3f

def z1052 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xa70e0e07fe041fff 0x34e1c1c0ffc083ff

def z1053 : W := mkw 0x27fdffb760008020 0x04ffbff6ec001004 0xe7ffffffe0058063 0xfcfffffffc00b00c

def z1054 : W := mkw 0x08020048916db6ed 0x61004009122db6dd 0x0800000011e59ffc 0x01000000023cb3ff

def z1055 : W := mkw 0x27fdbf3360000000 0x04ffb7e66c000000 0xe7ff3ffbe0000002 0xfcffe7ff7c000000

def z1056 : W := mkw 0x15b00f680bb01d02 0x02b601ed017603a0 0xeff00ff81fe01e06 0xfdfe01ff03fc03c0

def z1057 : W := mkw 0x235dffb760000000 0x046bbff6ec000000 0xe0cfffffe0000003 0xbc19fffffc000000

def z1058 : W := mkw 0x0154cfb500000000 0x002a99f6a0000000 0xe0cecfff80000003 0xbc19d9fff0000000

def z1059 : W := mkw 0x06eda0000cd34000 0x00ddb400019a6800 0xdffff0000ffbe001 0xfbfffe0001ff7c00

def z1060 : W := mkw 0x27fdffb768d14000 0x04ffbff6ed1a2800 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z1061 : W := mkw 0x27fdffb762000900 0x04ffbff6ec400120 0xe7ffffffe0001f83 0xfcfffffffc0003f0

def z1062 : W := mkw 0x0802004891249661 0x41004009122492cc 0x0000000010041e64 0x00000000020083cc

def z1063 : W := mkw 0x15b01f682bb83d8e 0x22b603ed057707b1 0xfff1fff87fffff9f 0xfffe3fff0ffffff3

def z1064 : W := mkw 0x37fdffb768980086 0x06ffbff6ed130010 0xe7ffffffe0180003 0xfcfffffffc030000

def z1065 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x0000000000059e60 0x000000000000b3cc

def z1066 : W := mkw 0x101053ec2128b4ae 0x22020a7d84251695 0x9831f7fc611ff1ff 0xd3063eff8c23fe3f

def z1067 : W := mkw 0x37fdffb76a900902 0x06ffbff6ed520120 0xe7ffffffee000003 0xfcfffffffdc00000

def z1068 : W := mkw 0x0eefa0119cd74241 0x41ddf402339ae848 0xdffff0039fffe005 0xfbfffe0073fffc00

def z1069 : W := mkw 0x000050842000a028 0x20000a1084001405 0x9831f604611ff1ff 0xd3063ec08c23fe3f

def z1070 : W := mkw 0x04e6a0001cd74000 0x009cd400039ae800 0xdff0f0001fffe004 0xfbfe1e0003fffc00

def z1071 : W := mkw 0x27fdffb76000a028 0x24ffbff6ec001405 0xe7ffffffe001e003 0xfcfffffffc003c00

def z1072 : W := mkw 0x04e6a00018d54000 0x009cd400031aa800 0xdffef0001ffde005 0xfbffde0003ffbc00

def z1073 : W := mkw 0x15b01f682bb83d8e 0x22b603ed057707b1 0xfff13ffc7ffe7fff 0xfffe27ff8fffcfff

def z1074 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x8800000411e59e67 0x11000000823cb3cc

def z1075 : W := mkw 0x15b00f680bb8bdae 0x22b601ed017717b5 0xfff00ff81ff9ff86 0xfffe01ff03ff3ff0

def z1076 : W := mkw 0x24f4f3b520000000 0x049e9e76a4000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1077 : W := mkw 0x15b00f280ab00d02 0x02b601e5015601a0 0xfff00ff81ff80e06 0xfffe01ff03ff01c0

def z1078 : W := mkw 0x35b01f6a6bb81d86 0x06b603ed4d7703b0 0xfff00ff87ff81f86 0xfffe01ff0fff03f0

def z1079 : W := mkw 0x03090c0240000000 0x0061218048000000 0xe7cf0fffe0000003 0xfcf9e1fffc000000

def z1080 : W := mkw 0x05e4ccb500000000 0x00bc9996a0000000 0xe7cec9ff80000003 0xbcf9d93ff0000000

def z1081 : W := mkw 0x225df3b760000000 0x044bbe76ec000000 0x000ff1ffe0000001 0x0001fe3ffc000000

def z1082 : W := mkw 0x234dfc9760000000 0x0469bf92ec000000 0xe7cfffffe0000003 0xfcf9fffffc000000

def z1083 : W := mkw 0x0044c09500410000 0x00089812a0082000 0xe8cec9ff81e18003 0xbd19d93ff03c3000

def z1084 : W := mkw 0x0044c09500000000 0x00089812a0000000 0x200ec9ff80000003 0x0401d93ff0000000

def z1085 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x68cec9ff81e59e63 0x8d19d93ff03cb3cc

def z1086 : W := mkw 0x04e4c09500000000 0x009c9812a0000000 0xe7fec9ff80000003 0xfcffd93ff0000000

def z1087 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0x7ff00ff81ff80f80 0xeffe01ff03ff01f0

def z1088 : W := mkw 0x05b00f6809b01400 0x00b601ed01360280 0xfff00ff81ff81e06 0xfffe01ff03ff03c0

def z1089 : W := mkw 0x2044d09760000000 0x04089a12ec000000 0xe0cec9ffe0000003 0xbc19d93ffc000000

def z1090 : W := mkw 0x03090c02c2000b51 0x806121805840016a 0xb70f0e07fe001fff 0x76e1e1c0ffc003ff

def z1091 : W := mkw 0x0846805991659661 0x4108d00b322cb2cc 0xe8ce09fb91e59e66 0xbd19c13f723cb3cc

def z1092 : W := mkw 0x15b00f280ab00d02 0x02b601e5015601a0 0x67f009f81ee00e00 0xacfe013f03dc01c0

def z1093 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xeff00ff81ff80e02 0xfdfe01ff03ff01c0

def z1094 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x9801060471e79fff 0x530020c08e3cf3ff

def z1095 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0xd8f1f7c471fff1ff 0xfb1e3ef88e3ffe3f

def z1096 : W := mkw 0x27fdffb76008208c 0x24ffbff6ec010411 0xe7ffffffe0186003 0xfcfffffffc030c00

def z1097 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xe0fff9ff80000003 0xfc1fff3ff0000000

def z1098 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0xe8ce09ff91e59e67 0xbd19c13ff23cb3cc

def z1099 : W := mkw 0x37fdffb76e9a4986 0x06ffbff6edd34930 0xf7ffffffee1a6183 0xfefffffffdc34c30

def z1100 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8cec9ff91fffe67 0xbf19d93ff23fffcc

def z1101 : W := mkw 0x0044c09500008020 0x00089812a0001004 0xe0cec9ff80058063 0xbc19d93ff000b00c

def z1102 : W := mkw 0x180200489bfd1fc7 0x43004009137fa3f8 0x180000001ff81f84 0x0300000003ff03f0

def z1103 : W := mkw 0x05a00c480bb01d00 0x00b40189017603a0 0xfff00ff81ff81f86 0xfffe01ff03ff03f0

def z1104 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xbf0f0e07ff1fffff 0x77e1e1c0ffe3ffff

def z1105 : W := mkw 0x0846d0ddb165b669 0x6108da1bb62cb6cd 0xe8cef9ff91e5fe67 0xbd19df3ff23cbfcc

def z1106 : W := mkw 0x0844c09500418020 0x41089812a0083004 0xe0cec9ff80018003 0xbc19d93ff0003000

def z1107 : W := mkw 0x27fdffb76000a028 0x24ffbff6ec001405 0xffffffffe11fe07f 0xfffffffffc23fc0f

def z1108 : W := mkw 0x27fdffb76008208c 0x24ffbff6ec010411 0xe7ffffffe000019b 0xfcfffffffc000033

def z1109 : W := mkw 0x27fdffb76a900900 0x04ffbff6ed520120 0xfffffffffff81f87 0xffffffffffff03f0

def z1110 : W := mkw 0x0846c0dd916db6ed 0x6108d81bb22db6dd 0xe8cec9ff91fdfe67 0xbd19d93ff23fbfcc

def z1111 : W := mkw 0x15b00f6a4bb81d96 0x82b601ed497703b2 0xfff00ff87ff81f9e 0xfffe01ff0fff03f3

def z1112 : W := mkw 0x27fdffb760080084 0x04ffbff6ec010010 0xf7ffffffe0180183 0xfefffffffc030030

def z1113 : W := mkw 0x15a00c680bb81d86 0x02b4018d017703b0 0xffc009f81ff81f86 0xbff8013f03ff03f0

def z1114 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x1831f7c0611ff1fc 0xc3063ef80c23fe3f

def z1115 : W := mkw 0x27fdffb766020910 0x84ffbff6ecc04122 0xf7ffffffee0611ff 0xfefffffffdc0c23f

def z1116 : W := mkw 0x27fdffb76e924910 0x84ffbff6edd24922 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z1117 : W := mkw 0x18020048936d9fe7 0x43004009126db3fc 0x0800000011e59fe4 0x01000000023cb3fc

def z1118 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8fef9ff91fdfe67 0xbd1fdf3ff23fbfcc

def z1119 : W := mkw 0x0802004899f5d661 0x41004009133ebacc 0x0800000011fdfe64 0x01000000023fbfcc

def z1120 : W := mkw 0x001013402108b0ac 0x2002026804211615 0x9831f600611ff1fd 0xd3063ec00c23fe3f

def z1121 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x68cec9ff91e58e61 0xad19d93ff23cb1cc

def z1122 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffff0047fffe07d 0xfbfffe008ffffc0f

def z1123 : W := mkw 0x07fdaf2240000000 0x00ffb5e448000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1124 : W := mkw 0x000000400108b0ac 0x2000000800211615 0x9831f604611ff1ff 0xd3063ec08c23fe3f

def z1125 : W := mkw 0x001053842008a0ac 0x20020a7084011415 0x9831f604611fe1fd 0xd3063ec08c23fc3f

def z1126 : W := mkw 0x15b00f6a4bb81d86 0x02b601ed497703b0 0xfff00ffffff81f86 0xfffe01ffffff03f0

def z1127 : W := mkw 0x06ede09500000000 0x00ddbc12a0000000 0xe7cec9ff80000003 0xbcf9d93ff0000000

def z1128 : W := mkw 0x27fdefb740000000 0x04ffbdf6e8000000 0xe7fecfff80000003 0xfcffd9fff0000000

def z1129 : W := mkw 0x10020048972e1fd7 0x8200400912e5c3fa 0x100000001e061ffc 0x0200000003c0c3ff

def z1130 : W := mkw 0x080250ccb165b669 0x61004a19962cb6cd 0x0801f00471e7fe7d 0x01003e008e3cffcf

def z1131 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xcffef0001ffde005 0xb9ffde0003ffbc00

def z1132 : W := mkw 0x0044c09500000000 0x00089812a0000000 0xf8fff9ff811fe007 0xff1fff3ff023fc00

def z1133 : W := mkw 0x0044c0dd01209420 0x0008981ba0241284 0xe8cec9ff91e59e67 0xbd19d93ff23cb3cc

def z1134 : W := mkw 0x04e4a00008d14000 0x009c9400011a2800 0x4ff0f0001ff9e000 0xa9fe1e0003ff3c00

def z1135 : W := mkw 0x0846d0ddb165b669 0x6108da1bb62cb6cd 0xf8cffffff1e7ffff 0xff19fffffe3cffff

def z1136 : W := mkw 0x224df09760000000 0x0449be12ec000000 0x200ff9ffe0000003 0x0401ff3ffc000000

def z1137 : W := mkw 0x034dcc9740000000 0x0069b992e8000000 0xe7cec9ff80000003 0xbcf9d93ff0000000

def z1138 : W := mkw 0x0802004893659f61 0x41004009126cb3ec 0x180000001fe59fe4 0x0300000003fcb3fc

def z1139 : W := mkw 0x0846c0dd916db6ed 0x6108d81bb22db6dd 0xf8cfcffff1ffffff 0xff19f9fffe3fffff

def z1140 : W := mkw 0x27fdaf3340000000 0x04ffb5e668000000 0x67ce0ffb80000002 0x2cf9c1ff70000000

def z1141 : W := mkw 0x31105fff6328bdae 0x26220bffec6517b5 0x20000fffe0001ffa 0x040001fffc0003ff

def z1142 : W := mkw 0x235dffb760000000 0x046bbff6ec000000 0xa70fffffe0000003 0x74e1fffffc000000

def z1143 : W := mkw 0x001053d52108b0ac 0x20020a7aa4211615 0xb831ffffe11ff1ff 0xd7063ffffc23fe3f

def z1144 : W := mkw 0x21105fb760000000 0x04220bf6ec000000 0xa00e0fffe0000003 0x3401c1fffc000000

def z1145 : W := mkw 0x0844c0dd81209661 0x4108981bb02412cc 0xe8cec9ff91e01e67 0xbd19d93ff23c03cc

def z1146 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x5ffef0001fffe004 0xabffde0003fffc00

def z1147 : W := mkw 0x06fdf39520000000 0x00dfbe72a4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1148 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xeffffffff1e00007 0xfdfffffffe3c0000

def z1149 : W := mkw 0x01020c02d2040b51 0x802041805a40816a 0xb70e0e07fe041fff 0x76e1c1c0ffc083ff

def z1150 : W := mkw 0x04e4c09508900000 0x009c9812a1120000 0xfffec9ff9ff80007 0xffffd93ff3ff0000

def z1151 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xb70ffe07fe07ffff 0x76e1ffc0ffc0ffff

def z1152 : W := mkw 0x0802004893659f71 0xc1004009126cb3ee 0x0800000011e59ffc 0x01000000023cb3ff

def z1153 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0x270f0e07fe061ffb 0x24e1e1c0ffc0c3ff

def z1154 : W := mkw 0x05f48f3100000000 0x00be91e620000000 0xe7fe0ffb80000002 0xfcffc1ff70000000

def z1155 : W := mkw 0x06ede0950c924000 0x00ddbc12a1924800 0xf7fff9ff8e1a6003 0xfeffff3ff1c34c00

def z1156 : W := mkw 0x0846c0dd9567d661 0x4108d81bb2acfacc 0xe8cec9ff91e7fe67 0xbd19d93ff23cffcc

def z1157 : W := mkw 0x1db20f689bfd9fe7 0x43b641ed137fb3fc 0x1f3006001ffd9fe4 0x43e600c003ffb3fc

def z1158 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x5ffff0000fffe001 0xcbfffe0001fffc00

def z1159 : W := mkw 0x04b0034809b81484 0x0096006901370290 0xfff00ff81ff81f86 0xfffe01ff03ff03f0

def z1160 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0xdffef0001ff9e004 0xfbffde0003ff3c00

def z1161 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xf7ffffffe01a6003 0xfefffffffc034c00

def z1162 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7cecfffe0000003 0xbcf9d9fffc000000

def z1163 : W := mkw 0x04e6800018d50000 0x009cd000031aa000 0xdffff0001fffe005 0xfbfffe0003fffc00

def z1164 : W := mkw 0x27b97fb760000000 0x04f72ff6ec000000 0xa73f3fffe0000003 0x74e7e7fffc000000

def z1165 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7fef9ff80000003 0xbcffdf3ff0000000

def z1166 : W := mkw 0x0802004897679f71 0xc100400912ecf3ee 0x080000001fe59e64 0x0100000003fcb3cc

def z1167 : W := mkw 0x06a920000c924000 0x00d5240001924800 0xdff1f0001fffe005 0xfbfe3e0003fffc00

def z1168 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x68cec9ff91e19e62 0xad19d93ff23c33cc

def z1169 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xf7ffffffe002019b 0xfefffffffc004033

def z1170 : W := mkw 0x0846c09d90650641 0x4108d813b20ca0c8 0xe8cec9ff91e58e07 0xbd19d93ff23cb1c0

def z1171 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x0800c00011e59e64 0x01001800023cb3cc

def z1172 : W := mkw 0x0846805991651641 0x4108d00b322ca2c8 0x60ce09fb90e01e02 0x2c19c13f721c03c0

def z1173 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7fe0fffe0000002 0xfcffc1fffc000000

def z1174 : W := mkw 0x180200489bfdbfef 0x63004009137fb7fd 0x180000001ffffffc 0x0300000003ffffff

def z1175 : W := mkw 0x07b95fa660000000 0x00f72bf4cc000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1176 : W := mkw 0x2154dfb760000000 0x042a9bf6ec000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1177 : W := mkw 0x080240cc91659661 0x41004819922cb2cc 0x0800c00411e59e65 0x01001800823cb3cc

def z1178 : W := mkw 0x0002004897261f51 0x8000400912e4c3ea 0x180000001fe61ffc 0x0300000003fcc3ff

def z1179 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xf8cecfff91e59fe7 0xff19d9fff23cb3fc

def z1180 : W := mkw 0x27fdffb768900000 0x04ffbff6ed120000 0xf7ffffffee180003 0xfefffffffdc30000

def z1181 : W := mkw 0x180200489bf59f63 0x43004009137eb3ec 0x080000001fe59e64 0x0100000003fcb3cc

def z1182 : W := mkw 0x06eda00008d14000 0x00ddb400011a2800 0xdffff0001ff9e005 0xfbfffe0003ff3c00

def z1183 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0x1031f7c4601ff1fb 0x42063ef88c03fe3f

def z1184 : W := mkw 0x001053cc2128b4ac 0x20020a7984251695 0xb831fffc611fffff 0xd7063fff8c23ffff

def z1185 : W := mkw 0x0046c0dd11651400 0x0008d81ba22ca280 0xe8cec9ff91e59e07 0xbd19d93ff23cb3c0

def z1186 : W := mkw 0x24f4f3b520000000 0x049e9e76a4000000 0x40fef1ff80000001 0x881fde3ff0000000

def z1187 : W := mkw 0x0a4fc097d4478271 0xc149f812fa88f04e 0x000ec00780058061 0x0001d800f000b00c

def z1188 : W := mkw 0x37fdffb76e9a0996 0x86ffbff6edd34132 0xf7ffffffee1a019b 0xfefffffffdc34033

def z1189 : W := mkw 0x024dc09740000000 0x0049b812e8000000 0xe0cfc9ffe0000003 0xbc19f93ffc000000

def z1190 : W := mkw 0x06efa0001cd74000 0x00ddf400039ae800 0x5ffff0001ffbe000 0xebfffe0003ff7c00

def z1191 : W := mkw 0x08020048976fbffd 0xe100400912edf7ff 0x180000001ffffffc 0x0300000003ffffff

def z1192 : W := mkw 0x100200489fff5fd7 0x8200400913ffebfa 0x180000001ffffffc 0x0300000003ffffff

def z1193 : W := mkw 0x0846d0ddb165b669 0x6108da1bb62cb6cd 0xe8cec9fff1e59e7f 0xbd19d93ffe3cb3cf

def z1194 : W := mkw 0x06eda0000cd34000 0x00ddb400019a6800 0x4ff0f0000ff9e000 0x89fe1e0001ff3c00

def z1195 : W := mkw 0x235ddfb760000000 0x046bbbf6ec000000 0xe7cfcfffe0000003 0xfcf9f9fffc000000

def z1196 : W := mkw 0x37fdffb76a980986 0x06ffbff6ed530130 0xf7fffffffe181f87 0xfeffffffffc303f0

def z1197 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x0000000010e01e60 0x00000000021c03cc

def z1198 : W := mkw 0x0144cc9502000900 0x00289992a0400120 0xf7cecfff9e001f87 0xfef9d9fff3c003f0

def z1199 : W := mkw 0x0802004895679661 0x4100400912acf2cc 0x180000001fe79e64 0x0300000003fcf3cc

def z1200 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0x68cec9fb91e59e64 0xad19d93f723cb3cc

def z1201 : W := mkw 0x0046c0dd91241641 0x0008d81bb22482c8 0xe8cec9ff91e41e67 0xbd19d93ff23c83cc

def z1202 : W := mkw 0x11100f6803281d86 0x022201ed006503b0 0xffc00ff81fe01f86 0xfff801ff03fc03f0

def z1203 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xe7fff9fb80000001 0xfcffff3f70000000

def z1204 : W := mkw 0x17b90f224e9a0996 0x82f721e449d34132 0x173006000e180180 0x42e600c001c30030

def z1205 : W := mkw 0x07b90f2240000000 0x00f721e448000000 0xe7fe0ffb80000002 0xfcffc1ff70000000

def z1206 : W := mkw 0x0846801990650641 0x4108d003320ca0c8 0xe0ce09fb90e00e02 0xbc19c13f721c01c0

def z1207 : W := mkw 0x081053dd2128b4ac 0x61020a7ba4251695 0x9831f7fc611ff1ff 0xd3063eff8c23fe3f

def z1208 : W := mkw 0x04e4e09508d14000 0x009c9c12a11a2800 0xe8fef9ff81f9e003 0xbd1fdf3ff03f3c00

def z1209 : W := mkw 0x27edecb740000000 0x04fdbd96e8000000 0x67ce09ff80000002 0x2cf9c13ff0000000

def z1210 : W := mkw 0x27edecb740000000 0x04fdbd96e8000000 0xe7cfcfffe0000003 0xfcf9f9fffc000000

def z1211 : W := mkw 0x0a4fd097f447a279 0xe149fa12fe88f44f 0x000ff007e007e079 0x0001fe00fc00fc0f

def z1212 : W := mkw 0x001013002008208c 0x2002026004010411 0x9831f604611ff1ff 0xd3063ec08c23fe3f

def z1213 : W := mkw 0x180200489fffdfe7 0x4300400913fffbfc 0x180000001fffffe4 0x0300000003fffffc

def z1214 : W := mkw 0x04a0000008900000 0x0094000001120000 0xdff0f0001ff9e004 0xfbfe1e0003ff3c00

def z1215 : W := mkw 0x27edecb740000000 0x04fdbd96e8000000 0xe7fff9ff80000003 0xfcffff3ff0000000

def z1216 : W := mkw 0x27b95fb760000000 0x04f72bf6ec000000 0xe7ff0fffe0000003 0xfcffe1fffc000000

def z1217 : W := mkw 0x0802004895679671 0xc100400912acf2ce 0x0800000011e79e7c 0x01000000023cf3cf

def z1218 : W := mkw 0x06efa0025cd74000 0x00ddf4004b9ae800 0xdffff007ffffe005 0xfbfffe00fffffc00

def z1219 : W := mkw 0x27fdffb7660a299c 0xa4ffbff6ecc14533 0xf7ffffffee1a619b 0xfefffffffdc34c33

def z1220 : W := mkw 0x224ff097f4474251 0x8449fe12fe88e84a 0x000ff007e007e079 0x0001fe00fc00fc0f

def z1221 : W := mkw 0x37b92f224a980986 0x06f725e449530130 0x173006000e180180 0x42e600c001c30030

def z1222 : W := mkw 0x03094c9740000000 0x00612992e8000000 0xa70f0fffe0000003 0x74e1e1fffc000000

def z1223 : W := mkw 0x27fdffb766020910 0x84ffbff6ecc04122 0xe7ffffffee000003 0xfcfffffffdc00000

def z1224 : W := mkw 0x15b00f680bb81d86 0x02b601ed017703b0 0xefc00ff81fe01f86 0xbdf801ff03fc03f0

def z1225 : W := mkw 0x0802004891659661 0x41004009122cb2cc 0x0800000001e58060 0x01000000003cb00c

def z1226 : W := mkw 0x100200489bbc1fc7 0x02004009137783f8 0x180000001ffc1fe4 0x0300000003ff83fc

def z1227 : W := mkw 0x17b91f226e9a299e 0xa2f723e44dd34533 0x173136006e1a6198 0x42e626c00dc34c33

def z1228 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67cfffffe0000003 0x2cf9fffffc000000

def z1229 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0xefffffffe119e003 0xfdfffffffc233c00

def z1230 : W := mkw 0x0054d3952008208c 0x200a9a72a4010411 0xf0ffffffe01a619b 0xfe1ffffffc034c33

def z1231 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z1232 : W := mkw 0x15a00c680bb01d02 0x02b4018d017603a0 0xffc00ff81fe01f86 0xfff801ff03fc03f0

def z1233 : W := mkw 0x001053c42108b0ac 0x20020a7884211615 0xb831ffc4711fffff 0xf7063ff88e23ffff

def z1234 : W := mkw 0x27edfcb760000000 0x04fdbf96ec000000 0xe7cff9ffe0000003 0xbcf9ff3ffc000000

def z1235 : W := mkw 0x0846804891659661 0x4108d009122cb2cc 0x48c0c00011e59e64 0x89181800023cb3cc

def z1236 : W := mkw 0x0ce6a04899f5d661 0x419cd409133ebacc 0x48f0f00011fdfe64 0x891e1e00023fbfcc

def z1237 : W := mkw 0x27fdffb760000000 0x04ffbff6ec000000 0x67ff3fffe0000002 0x6cffe7fffc000000

def z1238 : W := mkw 0x0846c0dd91659661 0x4108d81bb22cb2cc 0xe8ce09ff91e01e66 0xbd19c13ff23c03cc

def z1239 : W := mkw 0x030b0c02d6060b51 0x806161805ac0c16a 0xbf3f0e07ff1e1fff 0xf7e7e1c0ffe3c3ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z7,z4,z5,z6]),(0,[z0,z8,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z10]),(0,[z0,z11,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z12])],[(0,[z0,z2,z3,z4,z13,z5,z6]),(0,[z14,z0,z2,z3,z4,z5,z15]),(0,[z0,z2,z16,z4,z17,z5,z6]),(0,[z0,z2,z3,z18,z4,z5,z6]),(0,[z19,z0,z2,z3,z4,z5,z6]),(0,[z20,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z21,z6])],[(0,[z0,z2,z3,z4,z5,z6,z22])],[(0,[z0,z23,z2,z3,z4,z5,z6]),(0,[z24,z0,z2,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z26,z6]),(0,[z27,z0,z2,z3,z4,z5,z6])],[(0,[z0,z28,z3,z29,z4,z5,z6]),(0,[z14,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z30,z5,z6]),(0,[z0,z2,z31,z3,z4,z5,z6])],[(0,[z0,z32,z2,z3,z4,z5,z6]),(0,[z0,z33,z2,z3,z4,z5,z6]),(0,[z0,z34,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z7,z4,z5]),(1,[z0,z35,z2,z3,z36,z5]),(0,[z0,z2,z37,z3,z4,z5,z6]),(0,[z0,z2,z38,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z39,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z41,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z42,z5,z6])],[(0,[z0,z43,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z44,z4,z45,z6]),(0,[z0,z2,z3,z4,z5,z46,z6]),(0,[z0,z2,z47,z3,z44,z4,z6])],[(0,[z0,z48,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z49,z50,z5,z6]),(0,[z0,z2,z3,z4,z51,z5,z6]),(0,[z0,z52,z2,z3,z53,z5,z6]),(0,[z0,z35,z2,z3,z4,z54,z5])],[(0,[z55,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z56,z5,z6]),(0,[z0,z35,z57,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z58,z6]),(1,[z0,z2,z3,z44,z59,z6])],[(0,[z2,z60,z3,z25,z4,z5,z6]),(0,[z24,z2,z60,z3,z4,z5,z6]),(0,[z0,z61,z2,z3,z4,z5,z6]),(0,[z0,z2,z62,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z63,z64,z6]),(0,[z65,z66,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z67,z5,z6])],[(1,[z0,z2,z3,z4,z5,z68]),(0,[z0,z69,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z70,z6]),(0,[z0,z2,z71,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z13,z6]),(0,[z0,z72,z2,z3,z4,z5,z6]),(0,[z0,z73,z2,z4,z74,z5,z6])],[(0,[z0,z2,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z76,z4,z5,z6]),(0,[z0,z73,z2,z3,z9,z4,z5])],[(0,[z77,z0,z2,z78,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z79,z6]),(0,[z0,z80,z2,z3,z4,z5,z6])]],
   [[(0,[z81,z0,z2,z3,z82,z5,z6]),(0,[z0,z2,z3,z4,z83,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z84]),(0,[z0,z2,z3,z4,z85,z5,z6]),(0,[z0,z2,z3,z86,z4,z5,z6]),(0,[z87,z0,z2,z3,z4,z5,z6]),(1,[z88,z0,z35,z2,z3,z5]),(0,[z0,z2,z3,z4,z89,z5,z6])],[(0,[z90,z0,z2,z3,z4,z5,z6]),(0,[z14,z0,z2,z3,z4,z91,z6]),(0,[z92,z0,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z93,z4,z5,z6]),(0,[z0,z94,z2,z3,z4,z5,z6])],[(1,[z14,z2,z3,z36,z5,z6]),(1,[z0,z2,z3,z4,z5,z95]),(0,[z0,z2,z3,z4,z5,z96,z6]),(0,[z0,z2,z3,z4,z5,z97,z6])],[(0,[z81,z0,z2,z3,z4,z5,z98]),(0,[z81,z2,z3,z25,z4,z5,z6]),(0,[z0,z2,z99,z3,z4,z5,z6]),(0,[z92,z14,z2,z3,z4,z5,z6]),(0,[z100,z0,z2,z3,z4,z5,z6]),(0,[z101,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z102,z3,z4,z5,z6])],[(0,[z81,z0,z103,z3,z4,z5,z6]),(0,[z0,z2,z3,z104,z4,z5,z6]),(0,[z0,z2,z3,z4,z105,z45,z6]),(1,[z106,z0,z2,z3,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z107]),(0,[z108,z0,z2,z3,z4,z5,z6])],[(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z52,z2,z3,z9,z4,z5]),(0,[z0,z2,z110,z3,z4,z5,z111])],[(1,[z0,z2,z3,z4,z112,z6]),(0,[z0,z2,z3,z4,z113,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z15]),(0,[z0,z35,z2,z3,z4,z5,z45]),(0,[z92,z2,z3,z4,z63,z5,z6]),(0,[z0,z2,z114,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z53,z4,z5]),(0,[z0,z2,z3,z4,z115,z5,z6])],[(0,[z0,z116,z2,z3,z4,z5,z6]),(0,[z0,z117,z2,z3,z44,z4,z6])]],
   [[(0,[z66,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z118,z6])],[(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z119,z2,z3,z4,z5,z6]),(1,[z120,z0,z3,z4,z5,z121]),(0,[z20,z0,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z122,z6])],[(0,[z123,z0,z2,z3,z50,z5,z6]),(0,[z0,z2,z3,z36,z17,z5,z6]),(0,[z0,z2,z3,z4,z124,z5,z6]),(0,[z0,z2,z110,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z125])],[(0,[z0,z126,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z127]),(0,[z128,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z129]),(0,[z0,z130,z2,z16,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z6])],[(0,[z14,z0,z35,z2,z3,z4,z5]),(1,[z0,z130,z16,z4,z5,z6]),(0,[z0,z2,z3,z49,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z131]),(0,[z0,z2,z3,z4,z5,z132,z6]),(0,[z0,z2,z3,z133,z4,z5,z6])],[(0,[z77,z0,z2,z3,z4,z5,z6]),(0,[z134,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z135]),(0,[z0,z2,z3,z136,z4,z5,z6]),(0,[z137,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z138,z3,z9,z4,z5])],[(0,[z139,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z4,z5,z6]),(1,[z0,z2,z140,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z141,z6])],[(0,[z0,z2,z3,z142,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z143,z6]),(0,[z0,z2,z144,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z145]),(0,[z0,z146,z2,z3,z4,z5,z6]),(0,[z0,z2,z147,z3,z4,z5,z6]),(0,[z148,z0,z2,z3,z9,z4,z5])]],
   [[(0,[z0,z149,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z121]),(0,[z0,z2,z3,z4,z5,z150,z6]),(0,[z0,z2,z3,z4,z151,z5,z6])],[(0,[z0,z2,z3,z4,z5,z152,z6]),(0,[z0,z2,z153,z3,z4,z5,z6]),(0,[z0,z130,z2,z29,z4,z5,z6])],[(0,[z0,z2,z3,z154,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z45]),(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z0,z156,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z53,z4,z5]),(0,[z0,z157,z2,z4,z17,z5,z6]),(0,[z0,z2,z158,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z159]),(0,[z0,z160,z2,z3,z4,z5,z6]),(0,[z161,z0,z2,z3,z9,z4,z5])],[(0,[z0,z2,z3,z78,z4,z5,z6]),(0,[z0,z35,z2,z3,z50,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z162]),(0,[z109,z0,z52,z3,z4,z5,z6]),(0,[z106,z0,z2,z3,z5,z107,z6]),(0,[z0,z2,z3,z4,z163,z5,z6]),(1,[z0,z2,z3,z9,z5,z164]),(0,[z165,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z60,z29,z4,z5,z6]),(0,[z166,z0,z2,z3,z4,z5,z6]),(0,[z167,z0,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z168]),(0,[z0,z2,z3,z4,z5,z6,z169]),(0,[z0,z2,z3,z9,z170,z4,z5])],[(0,[z0,z2,z47,z16,z4,z5,z6]),(0,[z171,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z172,z6]),(0,[z0,z2,z3,z9,z4,z17,z5]),(0,[z88,z0,z2,z3,z44,z5,z6]),(0,[z0,z2,z173,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z174,z5,z6]),(0,[z0,z2,z3,z4,z5,z175,z6]),(0,[z176,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z177,z4,z5,z6]),(0,[z178,z0,z2,z3,z4,z5,z6]),(0,[z0,z179,z2,z3,z4,z5,z6]),(0,[z0,z35,z52,z2,z3,z4,z5]),(1,[z0,z2,z180,z3,z4,z6])]],
   [[(0,[z77,z0,z2,z3,z181,z5,z6]),(0,[z0,z2,z3,z4,z5,z182,z6]),(0,[z88,z0,z2,z3,z4,z63,z6]),(0,[z0,z2,z3,z4,z183,z5,z6]),(0,[z0,z146,z2,z3,z4,z105,z6]),(0,[z0,z35,z146,z2,z3,z4,z5]),(0,[z0,z35,z2,z3,z4,z5,z184])],[(0,[z0,z185,z2,z3,z4,z5,z6]),(0,[z0,z186,z2,z3,z4,z5,z6]),(0,[z0,z187,z2,z3,z4,z5,z6])],[(0,[z188,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z189,z5,z6]),(0,[z0,z2,z3,z4,z5,z190,z6]),(0,[z0,z3,z53,z4,z191,z5,z6]),(0,[z0,z117,z2,z192,z4,z5,z6]),(0,[z0,z193,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z194,z5,z6]),(0,[z28,z2,z60,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z195,z6]),(0,[z0,z2,z3,z4,z5,z121,z143]),(0,[z0,z2,z47,z29,z4,z5,z6]),(0,[z0,z2,z140,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z196,z5,z6]),(0,[z0,z197,z2,z3,z4,z5,z6]),(0,[z0,z198,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z5,z199,z107,z6]),(0,[z200,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z201,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z202,z6]),(0,[z0,z2,z203,z3,z4,z5,z6]),(0,[z109,z0,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z74,z5,z6])],[(0,[z0,z2,z3,z204,z4,z5,z6]),(0,[z0,z130,z2,z3,z9,z4,z5]),(0,[z205,z0,z2,z3,z4,z5,z6])],[(0,[z0,z130,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z206,z4,z5,z6]),(0,[z207,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z191,z5,z6]),(0,[z0,z2,z3,z208,z4,z5,z6]),(0,[z0,z2,z3,z209,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z210])]],
   [[(0,[z0,z35,z2,z3,z25,z4,z5]),(0,[z211,z0,z2,z3,z4,z5,z6]),(0,[z212,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z213,z4,z5,z6]),(0,[z0,z73,z2,z3,z4,z74,z6]),(0,[z0,z35,z2,z3,z4,z5,z111]),(0,[z0,z2,z3,z9,z4,z5,z168])],[(0,[z214,z0,z2,z3,z4,z5,z6]),(0,[z0,z57,z2,z3,z4,z5,z184]),(0,[z0,z2,z215,z3,z4,z5,z6]),(0,[z0,z119,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z9,z4,z5,z216])],[(0,[z14,z0,z2,z3,z4,z5,z217]),(0,[z0,z2,z3,z44,z4,z63,z6]),(0,[z120,z0,z2,z3,z4,z5,z184]),(0,[z0,z2,z3,z4,z5,z6,z218])],[(1,[z0,z2,z78,z4,z5,z6]),(0,[z0,z28,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z219,z6]),(0,[z0,z2,z29,z4,z74,z5,z6]),(0,[z0,z2,z3,z4,z5,z220,z6]),(0,[z0,z52,z2,z3,z59,z5,z6]),(0,[z0,z2,z3,z59,z5,z164,z6]),(0,[z0,z35,z2,z3,z4,z221,z5])],[(0,[z92,z222,z2,z3,z4,z5,z6]),(0,[z0,z2,z223,z3,z4,z5,z6]),(0,[z120,z0,z57,z3,z4,z5,z6])],[(0,[z77,z0,z2,z3,z4,z112,z6]),(0,[z77,z0,z35,z2,z3,z4,z5]),(0,[z224,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z225,z6]),(0,[z0,z2,z226,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z227,z5,z6]),(0,[z0,z35,z2,z3,z9,z4,z5])],[(0,[z0,z2,z3,z4,z50,z5,z6]),(0,[z88,z0,z2,z3,z36,z5,z6]),(0,[z0,z2,z3,z4,z5,z228,z6])],[(0,[z0,z2,z3,z229,z4,z5,z6]),(0,[z0,z230,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z231]),(0,[z0,z2,z3,z232,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z233,z6]),(0,[z0,z2,z47,z3,z9,z4,z5]),(0,[z0,z2,z3,z234,z4,z5,z6]),(0,[z88,z0,z2,z3,z5,z164,z6])],[(0,[z0,z2,z3,z4,z63,z235,z6]),(0,[z65,z0,z2,z3,z4,z5,z143]),(0,[z0,z236,z2,z3,z4,z5,z6]),(0,[z88,z0,z2,z3,z9,z4,z5])],[(0,[z0,z2,z3,z4,z237,z5,z6]),(0,[z238,z0,z2,z3,z4,z5,z6]),(0,[z120,z0,z2,z3,z4,z5,z111]),(0,[z0,z2,z3,z4,z54,z64,z6])],[(0,[z0,z2,z239,z3,z4,z5,z6]),(0,[z240,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z241,z5,z6]),(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z243,z3,z4,z5,z6]),(0,[z0,z244,z2,z3,z4,z5,z6])],[(1,[z0,z245,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z246,z6]),(0,[z0,z117,z2,z247,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z248,z6])],[(0,[z249,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z105,z63,z6]),(0,[z0,z2,z3,z4,z5,z132,z143]),(0,[z250,z0,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z235]),(0,[z0,z35,z73,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z251,z6])],[(0,[z252,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z15]),(0,[z0,z2,z3,z4,z5,z253,z6]),(0,[z254,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z255,z5,z6]),(0,[z0,z57,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z256]),(0,[z257,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z258,z5,z6])],[(0,[z259,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z260,z4,z5,z6]),(0,[z120,z0,z2,z3,z9,z4,z5]),(0,[z178,z0,z35,z2,z3,z4,z5]),(0,[z0,z35,z2,z261,z3,z4,z5])]],
   [[(0,[z0,z75,z3,z29,z4,z5,z6]),(0,[z222,z0,z2,z3,z4,z45,z6]),(0,[z0,z262,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z263,z4,z5,z6]),(0,[z0,z35,z2,z3,z49,z4,z5]),(0,[z0,z2,z264,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z5,z164,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z265,z6]),(0,[z0,z35,z2,z75,z3,z4,z5]),(0,[z0,z266,z2,z3,z4,z5,z6]),(0,[z0,z267,z2,z3,z4,z5,z6]),(0,[z0,z268,z2,z3,z4,z5,z6]),(1,[z269,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z270])],[(0,[z271,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z184,z168])],[(0,[z77,z272,z2,z3,z4,z5,z6]),(0,[z0,z273,z2,z3,z4,z50,z5]),(0,[z0,z274,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z275,z4,z5,z6]),(0,[z276,z0,z2,z3,z4,z5,z6])],[(0,[z277,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z278,z3,z4,z5,z6]),(0,[z0,z279,z2,z3,z4,z5,z6]),(0,[z0,z280,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z281,z4,z5,z6]),(0,[z0,z2,z282,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z42,z5]),(0,[z0,z2,z283,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z284,z5,z6]),(0,[z0,z2,z16,z60,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z285,z6]),(0,[z0,z2,z3,z4,z5,z286,z6]),(0,[z0,z2,z3,z4,z54,z5,z168])],[(0,[z287,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z53,z36,z5,z6]),(0,[z0,z117,z2,z3,z9,z4,z5])],[(1,[z0,z273,z2,z3,z4,z5]),(0,[z0,z2,z3,z288,z4,z5,z6]),(0,[z0,z2,z3,z4,z289,z5,z6]),(0,[z0,z290,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z164,z6]),(0,[z0,z2,z3,z170,z4,z5,z6]),(0,[z0,z291,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z35,z28,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z292,z5,z6]),(0,[z0,z293,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z294,z4,z5,z107]),(1,[z0,z2,z3,z4,z295,z5]),(0,[z0,z2,z3,z4,z295,z5,z6]),(0,[z0,z57,z2,z261,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z235,z6]),(0,[z88,z27,z2,z3,z4,z5,z6]),(0,[z211,z0,z35,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z296,z5,z6]),(0,[z0,z2,z3,z297,z4,z5,z6]),(0,[z120,z0,z2,z261,z3,z4,z5]),(0,[z0,z2,z3,z9,z4,z5,z121]),(0,[z0,z2,z47,z3,z4,z235,z6]),(0,[z0,z2,z3,z9,z4,z5,z235]),(0,[z0,z298,z2,z3,z4,z5,z6]),(0,[z0,z299,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z9,z5,z6])],[(0,[z0,z300,z2,z3,z4,z5,z6]),(0,[z0,z301,z2,z3,z4,z5,z6]),(0,[z0,z52,z2,z3,z4,z5,z302]),(0,[z0,z2,z247,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z303,z6]),(1,[z0,z2,z3,z4,z5,z304])],[(0,[z0,z2,z3,z25,z9,z4,z5]),(0,[z305,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z306,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z162])],[(0,[z77,z0,z28,z3,z4,z5,z6]),(1,[z0,z2,z3,z181,z5,z6]),(0,[z0,z2,z3,z307,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z308,z6]),(0,[z0,z2,z3,z4,z5,z309,z6]),(0,[z0,z2,z261,z3,z4,z5,z143])],[(0,[z0,z2,z3,z4,z310,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z0,z2,z3,z4,z5,z121,z6]),(0,[z0,z2,z3,z4,z5,z6,z312]),(0,[z0,z2,z4,z74,z5,z235,z6]),(1,[z27,z2,z3,z4,z5,z6])],[(0,[z0,z2,z245,z3,z4,z5,z6]),(0,[z0,z313,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z91,z6])],[(0,[z0,z2,z3,z314,z4,z5,z6]),(0,[z0,z315,z2,z3,z4,z5,z6])]],
   [[(0,[z81,z0,z2,z3,z4,z5,z316]),(0,[z0,z2,z3,z4,z5,z6,z317]),(0,[z0,z35,z2,z3,z44,z4,z5])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z318]),(0,[z0,z2,z3,z4,z5,z6,z319]),(0,[z0,z2,z3,z4,z320,z5,z6]),(0,[z321,z0,z2,z3,z4,z5,z6]),(1,[z88,z0,z2,z3,z322,z6])],[(0,[z323,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z64,z6,z168])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(1,[z272,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z316]),(0,[z0,z35,z2,z3,z59,z5,z6]),(0,[z0,z2,z3,z324,z4,z5,z6])],[(0,[z0,z73,z2,z3,z4,z5,z6]),(1,[z0,z73,z2,z4,z74,z6])],[(0,[z0,z2,z325,z3,z4,z5,z6])],[(0,[z272,z0,z2,z3,z9,z4,z5]),(0,[z0,z35,z230,z2,z3,z4,z5]),(0,[z326,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z327]),(0,[z328,z0,z2,z3,z4,z5,z6])],[(0,[z272,z0,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z329,z5,z6]),(0,[z123,z2,z3,z4,z50,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z330]),(0,[z0,z2,z3,z4,z331,z5,z6]),(1,[z109,z0,z3,z191,z5,z6]),(0,[z20,z0,z2,z3,z4,z5,z132])]],
   [[(0,[z0,z2,z332,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z333,z6])],[(1,[z0,z2,z3,z4,z237,z6]),(0,[z0,z2,z3,z4,z5,z334,z6]),(0,[z0,z2,z3,z4,z5,z335,z6]),(1,[z0,z2,z3,z4,z5,z336]),(1,[z0,z35,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z6,z337]),(1,[z0,z2,z306,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z338,z6]),(0,[z0,z2,z339,z3,z4,z5,z6])],[(0,[z77,z81,z2,z3,z4,z5,z6]),(0,[z65,z0,z2,z3,z4,z5,z6]),(0,[z340,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z341,z5,z6]),(0,[z276,z0,z35,z2,z3,z4,z5])],[(0,[z77,z0,z2,z3,z4,z342,z6]),(1,[z0,z2,z3,z4,z343,z6]),(0,[z0,z2,z3,z49,z36,z5,z6]),(1,[z0,z2,z213,z4,z5,z6]),(0,[z0,z344,z2,z3,z4,z5,z6]),(0,[z0,z146,z2,z3,z4,z5,z327]),(0,[z0,z35,z2,z3,z4,z17,z5]),(0,[z0,z2,z3,z9,z44,z4,z5])],[(0,[z0,z2,z345,z3,z4,z5,z6]),(1,[z0,z2,z114,z4,z5,z6]),(1,[z0,z2,z110,z4,z5,z111])],[(0,[z0,z2,z3,z4,z346,z5,z6]),(0,[z347,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z348]),(1,[z0,z2,z3,z4,z5,z335]),(0,[z88,z0,z2,z47,z3,z4,z6])],[(0,[z0,z2,z138,z3,z17,z5,z6]),(0,[z0,z290,z35,z2,z3,z4,z5]),(0,[z0,z2,z349,z3,z4,z5,z6])]],
   [[(0,[z0,z130,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z350,z5,z6]),(0,[z0,z2,z3,z4,z5,z330,z184]),(0,[z0,z2,z351,z3,z4,z5,z6]),(0,[z88,z0,z2,z3,z4,z59,z6]),(0,[z0,z2,z3,z4,z352,z5,z6])],[(0,[z0,z35,z2,z3,z36,z4,z5]),(0,[z0,z2,z16,z4,z74,z5,z6]),(0,[z0,z353,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z44,z59,z5,z6])],[(0,[z0,z354,z2,z3,z4,z5,z6]),(0,[z0,z2,z16,z3,z9,z4,z5]),(1,[z0,z146,z3,z4,z107,z6]),(0,[z0,z2,z3,z49,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z127]),(0,[z355,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z356]),(0,[z0,z2,z138,z3,z4,z5,z6]),(0,[z0,z2,z3,z357,z4,z5,z6])],[(0,[z0,z2,z3,z358,z4,z5,z6]),(0,[z66,z2,z3,z4,z5,z6,z330]),(1,[z0,z2,z261,z3,z4,z168])],[(0,[z0,z2,z3,z9,z4,z5,z143]),(1,[z0,z2,z3,z4,z5,z286]),(0,[z148,z0,z2,z3,z4,z5,z6])],[(0,[z65,z0,z2,z3,z359,z5,z6]),(0,[z0,z2,z3,z4,z59,z5,z6])],[(0,[z0,z2,z360,z3,z4,z5,z6]),(0,[z0,z2,z3,z361,z4,z5,z6]),(0,[z362,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z47,z4,z235,z6]),(1,[z0,z244,z2,z3,z5,z6])]],
   [[(0,[z161,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z363,z3,z4,z5,z6]),(0,[z364,z0,z2,z3,z4,z5,z6]),(0,[z0,z365,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z330,z111]),(0,[z0,z2,z3,z4,z366,z5,z6]),(0,[z20,z0,z2,z110,z4,z5,z6]),(0,[z88,z0,z35,z2,z3,z5,z6]),(0,[z0,z35,z160,z2,z3,z4,z5]),(0,[z0,z2,z3,z367,z4,z5,z6])],[(0,[z222,z0,z2,z3,z4,z63,z6]),(0,[z0,z35,z2,z3,z4,z191,z5]),(0,[z0,z2,z3,z4,z5,z368,z6])],[(0,[z0,z369,z2,z3,z4,z5,z6]),(0,[z0,z370,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z371,z6]),(0,[z0,z2,z3,z372,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z373,z6]),(0,[z0,z2,z3,z4,z5,z374,z6])],[(0,[z123,z0,z2,z3,z36,z5,z6]),(0,[z222,z2,z3,z4,z5,z45,z6]),(0,[z0,z2,z3,z4,z5,z375,z6]),(0,[z0,z2,z3,z4,z5,z376,z6]),(0,[z0,z2,z3,z4,z5,z377,z6])],[(0,[z0,z2,z3,z4,z378,z5,z6]),(0,[z0,z2,z3,z9,z36,z4,z5]),(0,[z0,z2,z379,z3,z4,z5,z6]),(0,[z0,z380,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z381])],[(0,[z0,z2,z3,z4,z63,z5,z6]),(0,[z0,z35,z2,z3,z4,z63,z5]),(0,[z0,z3,z4,z5,z121,z6,z184]),(0,[z0,z2,z4,z5,z132,z6,z111]),(1,[z0,z2,z282,z3,z4,z5]),(0,[z0,z2,z261,z3,z4,z5,z6])],[(0,[z123,z0,z2,z3,z9,z4,z5]),(1,[z0,z2,z3,z4,z5,z217]),(0,[z0,z2,z180,z3,z4,z17,z6]),(0,[z0,z2,z3,z4,z382,z5,z6]),(0,[z0,z244,z2,z3,z5,z6,z168])]],
   [[(0,[z383,z0,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z60,z4,z5,z6]),(0,[z0,z2,z3,z7,z4,z50,z5]),(0,[z0,z2,z3,z4,z5,z384,z6]),(0,[z0,z2,z261,z3,z4,z54,z6]),(0,[z0,z2,z261,z3,z4,z6,z168]),(1,[z0,z2,z3,z5,z6,z385])],[(0,[z81,z0,z2,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z45,z107,z6]),(0,[z0,z2,z3,z4,z386,z5,z6]),(0,[z0,z35,z2,z3,z29,z4,z5]),(0,[z0,z2,z3,z4,z5,z111,z168])],[(0,[z0,z2,z3,z4,z387,z5,z6]),(1,[z0,z2,z3,z4,z388,z6]),(0,[z0,z389,z2,z3,z4,z5,z6]),(0,[z0,z2,z390,z3,z4,z5,z6]),(0,[z200,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z391])],[(1,[z66,z2,z3,z4,z5,z330]),(0,[z65,z0,z35,z2,z3,z4,z5]),(0,[z392,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z393,z4,z5,z6]),(0,[z20,z0,z2,z3,z4,z5,z111]),(0,[z0,z35,z2,z3,z133,z4,z5]),(0,[z0,z2,z3,z9,z4,z4,z5])],[(0,[z77,z0,z2,z394,z4,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z60,z3,z9,z4,z5]),(0,[z0,z130,z2,z3,z4,z5,z6]),(0,[z0,z146,z2,z3,z4,z107,z6]),(0,[z0,z2,z3,z395,z9,z4,z5])],[(0,[z0,z35,z2,z3,z36,z5,z6]),(0,[z0,z2,z396,z3,z4,z5,z6]),(1,[z65,z2,z3,z4,z5,z143]),(0,[z0,z2,z3,z4,z397,z5,z6]),(0,[z0,z2,z3,z9,z4,z191,z5]),(0,[z0,z2,z398,z3,z4,z5,z6])],[(0,[z0,z2,z3,z50,z59,z5,z6]),(0,[z66,z0,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z399,z6]),(0,[z0,z2,z3,z4,z5,z391,z6]),(0,[z0,z2,z3,z4,z400,z5,z6])],[(0,[z2,z3,z36,z4,z50,z5,z6]),(0,[z401,z0,z2,z3,z4,z5,z6]),(0,[z402,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z403,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z404]),(0,[z88,z0,z117,z2,z3,z4,z6]),(0,[z405,z0,z2,z3,z4,z5,z6])],[(0,[z0,z28,z2,z3,z4,z5,z6]),(0,[z0,z2,z406,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z45,z6]),(0,[z0,z2,z3,z4,z5,z407,z6]),(0,[z0,z2,z3,z4,z5,z6,z408])],[(0,[z222,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z9,z4,z63,z5]),(0,[z0,z2,z3,z4,z54,z5,z143]),(0,[z0,z2,z409,z3,z4,z5,z6]),(0,[z0,z2,z3,z410,z4,z5,z6])],[(0,[z411,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z36,z191,z5,z6]),(1,[z0,z2,z3,z4,z5,z84]),(0,[z0,z2,z3,z4,z5,z132,z64]),(0,[z0,z35,z2,z3,z4,z5,z6])],[(0,[z412,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z413,z3,z4,z5,z6]),(0,[z0,z2,z16,z138,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z414,z6])],[(0,[z0,z2,z3,z4,z5,z415,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z416]),(0,[z0,z417,z2,z3,z4,z5,z6]),(0,[z0,z2,z418,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z419,z6]),(1,[z0,z2,z3,z82,z5,z6]),(0,[z0,z420,z2,z3,z4,z5,z6]),(0,[z0,z421,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z327])],[(0,[z28,z2,z75,z3,z4,z5,z6]),(0,[z422,z0,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z423,z6]),(0,[z0,z2,z3,z424,z4,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z143]),(0,[z120,z0,z3,z4,z5,z121,z6]),(0,[z88,z269,z2,z3,z4,z5,z6]),(0,[z88,z0,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z5,z6,z10])]],
   [[(1,[z0,z2,z3,z4,z342,z6]),(0,[z0,z2,z3,z4,z5,z425,z6]),(0,[z0,z426,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z121]),(0,[z0,z2,z138,z3,z4,z5,z335]),(0,[z161,z0,z35,z2,z3,z4,z5])],[(0,[z272,z28,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z98]),(0,[z0,z2,z427,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z428,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z429]),(0,[z0,z2,z3,z4,z430,z5,z6]),(0,[z0,z146,z117,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z431,z6]),(0,[z0,z2,z3,z432,z9,z4,z5])],[(1,[z0,z103,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z433,z6]),(1,[z0,z280,z2,z3,z4,z6]),(0,[z434,z0,z2,z3,z4,z5,z6])],[(0,[z24,z0,z2,z60,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z184]),(0,[z0,z157,z2,z3,z9,z4,z5])],[(0,[z435,z0,z2,z3,z4,z5,z6]),(0,[z24,z0,z2,z47,z4,z5,z6]),(0,[z0,z57,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z436,z6]),(0,[z0,z437,z2,z3,z4,z5,z6])],[(0,[z438,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z439]),(0,[z120,z0,z2,z3,z4,z5,z6])],[(0,[z77,z2,z60,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z440,z6]),(0,[z92,z0,z2,z3,z155,z5,z6]),(0,[z441,z0,z2,z3,z9,z4,z5])],[(0,[z0,z2,z3,z442,z4,z191,z5]),(0,[z0,z2,z3,z4,z5,z443,z6]),(0,[z0,z2,z3,z9,z4,z5,z6]),(0,[z444,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z445,z0,z2,z3,z4,z5,z6]),(0,[z272,z0,z28,z3,z4,z5,z6])],[(0,[z446,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z143,z184]),(0,[z0,z2,z3,z447,z4,z5,z6]),(0,[z0,z2,z16,z3,z4,z5,z286]),(0,[z0,z2,z3,z4,z5,z6,z448]),(0,[z0,z57,z2,z3,z4,z5,z121]),(0,[z0,z2,z3,z4,z5,z6,z449]),(0,[z450,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z44,z4,z5,z6]),(0,[z451,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z452,z5,z6]),(0,[z0,z2,z3,z4,z5,z91,z6]),(0,[z120,z0,z2,z3,z4,z5,z121]),(0,[z0,z453,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z17,z5,z6]),(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z455,z6]),(0,[z0,z2,z261,z3,z4,z5,z64]),(0,[z0,z2,z3,z4,z5,z6,z456])],[(0,[z0,z2,z3,z457,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z458]),(0,[z0,z2,z3,z4,z5,z121,z330]),(0,[z0,z16,z3,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z111])],[(0,[z81,z0,z2,z3,z104,z5,z6]),(0,[z0,z2,z3,z4,z5,z459,z6]),(0,[z123,z14,z2,z3,z4,z5,z6]),(0,[z65,z0,z2,z3,z4,z388,z6]),(0,[z0,z2,z3,z4,z5,z6,z460]),(0,[z0,z117,z2,z3,z4,z5,z6]),(0,[z461,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z462,z6]),(0,[z0,z2,z3,z59,z5,z322,z6])],[(0,[z81,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z463,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z464,z6]),(0,[z0,z2,z3,z4,z5,z6,z465])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z466,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z467]),(0,[z0,z2,z3,z4,z5,z6,z468]),(1,[z0,z2,z3,z359,z5,z6]),(0,[z0,z2,z3,z213,z4,z5,z6]),(0,[z0,z2,z3,z53,z4,z5,z6])]],
   [[(0,[z0,z469,z2,z3,z4,z5,z6]),(0,[z65,z0,z2,z3,z93,z5,z6]),(0,[z0,z2,z29,z4,z17,z5,z6]),(0,[z0,z35,z130,z2,z3,z4,z5]),(0,[z0,z2,z3,z470,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z471,z6]),(0,[z0,z2,z3,z9,z4,z352,z5])],[(0,[z0,z2,z3,z25,z4,z5,z6]),(0,[z0,z2,z472,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z143,z111]),(0,[z0,z2,z3,z4,z473,z5,z6]),(0,[z88,z0,z2,z3,z5,z322,z6])],[(0,[z0,z2,z3,z474,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z475,z6]),(0,[z476,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z9,z4,z477,z5])],[(1,[z123,z2,z3,z50,z5,z6]),(0,[z0,z2,z3,z4,z478,z5,z6]),(0,[z0,z2,z3,z479,z4,z5,z6]),(0,[z0,z35,z35,z2,z3,z4,z5])],[(0,[z480,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z105,z5,z6]),(0,[z0,z2,z138,z49,z4,z5,z6]),(0,[z0,z269,z2,z3,z4,z5,z6])],[(0,[z481,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z112,z6]),(0,[z0,z52,z2,z3,z4,z5,z84]),(0,[z0,z117,z2,z3,z4,z105,z6]),(0,[z0,z2,z47,z4,z5,z235,z6]),(0,[z482,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z483])],[(0,[z0,z2,z3,z4,z484,z5,z6]),(0,[z0,z2,z47,z3,z4,z5,z336]),(0,[z0,z2,z3,z9,z4,z5,z322]),(0,[z0,z2,z282,z3,z4,z5,z322])],[(0,[z0,z2,z3,z4,z485,z5,z6]),(0,[z0,z2,z3,z486,z4,z5,z6]),(0,[z0,z2,z3,z4,z487,z5,z6]),(0,[z488,z0,z2,z3,z4,z5,z6]),(0,[z0,z52,z3,z53,z4,z5,z6]),(0,[z0,z2,z489,z3,z4,z5,z6]),(0,[z88,z0,z35,z2,z3,z4,z5]),(0,[z0,z490,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z394,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z343,z6]),(0,[z0,z2,z3,z4,z491,z5,z6]),(0,[z0,z2,z3,z29,z9,z4,z5]),(1,[z0,z2,z3,z86,z4,z5]),(0,[z0,z492,z2,z3,z4,z5,z6]),(1,[z0,z35,z2,z3,z59,z5])],[(0,[z0,z2,z3,z4,z181,z5,z6]),(0,[z65,z0,z2,z3,z4,z5,z330]),(0,[z0,z2,z3,z442,z4,z5,z6]),(0,[z0,z2,z3,z4,z493,z5,z6])],[(0,[z0,z2,z3,z50,z17,z5,z6]),(1,[z0,z35,z2,z3,z50,z5]),(0,[z0,z2,z3,z50,z5,z164,z6]),(0,[z0,z2,z3,z9,z4,z5,z132]),(0,[z434,z0,z35,z2,z3,z4,z5])],[(0,[z92,z2,z3,z4,z50,z5,z6]),(0,[z0,z2,z3,z494,z4,z5,z6]),(0,[z0,z230,z2,z16,z4,z5,z6]),(0,[z0,z35,z157,z2,z3,z4,z5])],[(0,[z272,z0,z2,z3,z4,z5,z6]),(0,[z495,z0,z2,z3,z4,z5,z6]),(0,[z81,z24,z2,z3,z4,z5,z6]),(1,[z81,z2,z25,z4,z5,z6]),(0,[z0,z2,z496,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z143]),(0,[z0,z2,z3,z4,z497,z5,z6]),(0,[z498,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z54,z5,z6]),(0,[z499,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z132,z330]),(1,[z0,z57,z3,z4,z5,z184]),(0,[z120,z0,z35,z2,z3,z4,z5]),(0,[z0,z157,z2,z138,z4,z5,z6]),(0,[z0,z2,z47,z3,z4,z74,z6])],[(0,[z0,z52,z2,z3,z4,z5,z6]),(0,[z0,z146,z3,z4,z5,z107,z6]),(0,[z0,z2,z3,z4,z295,z5,z107]),(0,[z0,z2,z3,z500,z4,z5,z6]),(0,[z0,z501,z2,z3,z4,z5,z6]),(0,[z0,z2,z502,z3,z9,z4,z5])],[(0,[z0,z2,z3,z503,z4,z5,z6]),(0,[z24,z0,z2,z4,z74,z5,z6])]],
   [[(0,[z24,z0,z2,z3,z9,z4,z5])],[(0,[z0,z2,z3,z4,z5,z6,z504]),(0,[z66,z0,z2,z3,z4,z5,z6]),(0,[z505,z0,z2,z3,z4,z5,z6]),(0,[z0,z230,z2,z29,z4,z5,z6]),(0,[z0,z2,z506,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z507,z5,z6]),(0,[z0,z35,z2,z3,z4,z74,z5]),(0,[z0,z2,z508,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z509]),(0,[z451,z0,z35,z2,z3,z4,z5])],[(0,[z92,z0,z2,z3,z4,z63,z6]),(0,[z0,z157,z2,z3,z49,z5,z6]),(0,[z88,z0,z2,z3,z4,z322,z6]),(1,[z0,z2,z3,z4,z54,z64])],[(0,[z0,z35,z2,z60,z3,z4,z5]),(0,[z0,z510,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z294,z4,z5]),(0,[z0,z2,z3,z511,z4,z5,z6]),(0,[z0,z2,z110,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z512]),(0,[z0,z2,z3,z4,z5,z216,z6]),(0,[z0,z2,z3,z9,z4,z5,z64]),(0,[z0,z2,z3,z4,z5,z513,z6])],[(0,[z0,z2,z3,z4,z342,z5,z6]),(0,[z0,z2,z49,z4,z17,z5,z6]),(0,[z0,z35,z2,z47,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z514])],[(0,[z515,z0,z2,z3,z4,z5,z6])],[(0,[z0,z516,z2,z3,z4,z5,z6]),(0,[z0,z517,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z518,z6]),(1,[z0,z2,z3,z5,z199,z6])],[(1,[z24,z2,z60,z4,z5,z6]),(0,[z2,z3,z4,z50,z5,z45,z6]),(0,[z0,z2,z519,z3,z4,z5,z6]),(0,[z0,z35,z2,z520,z3,z4,z5]),(0,[z521,z0,z2,z3,z9,z4,z5])]],
   [[(0,[z0,z2,z16,z3,z4,z5,z6]),(1,[z0,z2,z3,z442,z4,z5]),(0,[z0,z2,z522,z3,z4,z5,z6]),(0,[z523,z0,z2,z3,z4,z5,z6])],[(0,[z524,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z98,z6]),(0,[z525,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z526,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z527]),(0,[z0,z2,z3,z4,z5,z6,z528])],[(0,[z0,z2,z3,z529,z4,z5,z6]),(0,[z109,z0,z2,z3,z59,z5,z6]),(0,[z0,z146,z2,z3,z44,z4,z6]),(0,[z0,z2,z530,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z531]),(0,[z0,z35,z2,z3,z4,z4,z5]),(0,[z0,z2,z3,z5,z6,z385,z168])],[(0,[z0,z2,z261,z3,z4,z45,z6]),(0,[z0,z2,z3,z532,z4,z5,z6]),(0,[z0,z2,z3,z4,z533,z5,z6])],[(0,[z0,z103,z2,z3,z4,z5,z6]),(0,[z14,z0,z2,z3,z50,z5,z6]),(0,[z0,z2,z261,z3,z4,z5,z330]),(0,[z0,z2,z534,z3,z4,z5,z6])],[(0,[z0,z2,z535,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z536,z6]),(0,[z0,z2,z3,z4,z5,z537,z6]),(0,[z0,z2,z3,z4,z74,z45,z6]),(0,[z0,z35,z2,z16,z3,z4,z5]),(0,[z109,z0,z3,z4,z191,z5,z6]),(0,[z0,z2,z3,z9,z4,z74,z5]),(0,[z0,z2,z3,z44,z4,z59,z6]),(0,[z0,z2,z3,z4,z5,z509,z6])],[(0,[z0,z2,z3,z4,z5,z388,z6]),(0,[z0,z230,z2,z3,z9,z4,z5]),(0,[z0,z538,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z539,z4,z5,z6]),(0,[z65,z0,z2,z3,z4,z484,z6]),(0,[z0,z2,z3,z294,z4,z5,z6]),(0,[z0,z2,z47,z3,z4,z5,z391]),(0,[z0,z2,z3,z4,z5,z6,z540]),(0,[z0,z2,z3,z232,z9,z4,z5])]],
   [[(0,[z14,z2,z3,z4,z5,z45,z6]),(0,[z0,z2,z541,z3,z4,z191,z5]),(0,[z0,z35,z2,z110,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z542,z6])],[(0,[z0,z130,z230,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z543,z5,z6]),(0,[z0,z2,z544,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z449])],[(0,[z545,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z217,z6]),(0,[z0,z2,z16,z3,z4,z5,z162]),(0,[z0,z2,z3,z9,z4,z59,z5])],[(0,[z92,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z546,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z59,z5,z527]),(0,[z0,z35,z2,z102,z3,z4,z5])],[(0,[z272,z0,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z9,z4,z50,z5]),(0,[z0,z57,z3,z4,z5,z6,z184]),(0,[z0,z547,z2,z3,z4,z5,z6])],[(0,[z0,z2,z394,z3,z4,z5,z6]),(0,[z123,z0,z2,z3,z4,z5,z6]),(0,[z548,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z549,z5,z6]),(0,[z0,z2,z3,z4,z550,z5,z6])],[(0,[z551,z0,z2,z3,z4,z5,z6]),(1,[z92,z2,z3,z4,z63,z6]),(0,[z0,z552,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z553]),(0,[z0,z2,z110,z3,z4,z5,z132]),(0,[z0,z2,z3,z4,z5,z554,z6])],[(0,[z0,z2,z3,z4,z5,z6,z555]),(0,[z0,z2,z3,z4,z5,z556,z6])]],
   [[(0,[z557,z0,z2,z3,z4,z5,z6]),(0,[z0,z52,z2,z3,z191,z5,z6]),(0,[z558,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z559,z4,z5,z6]),(0,[z0,z2,z3,z4,z54,z5,z64])],[(1,[z222,z2,z3,z4,z45,z6]),(1,[z0,z2,z3,z93,z5,z6])],[(0,[z0,z2,z60,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z45,z64,z6]),(0,[z0,z2,z3,z4,z189,z5,z6]),(0,[z0,z560,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z395,z4,z5,z6]),(0,[z0,z2,z110,z4,z5,z6,z111]),(0,[z0,z11,z2,z3,z9,z4,z5])],[(1,[z0,z52,z3,z53,z5,z6]),(0,[z20,z0,z2,z3,z9,z4,z5])],[(0,[z0,z2,z4,z561,z5,z45,z6]),(1,[z2,z3,z562,z4,z5,z6])],[(0,[z563,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z381,z6]),(0,[z0,z2,z3,z4,z5,z6,z385])],[(1,[z0,z2,z3,z4,z5,z316]),(0,[z14,z0,z2,z3,z9,z4,z5]),(0,[z2,z3,z4,z5,z143,z6,z330]),(0,[z0,z35,z117,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z564,z6])],[(0,[z0,z2,z3,z4,z5,z565,z6]),(0,[z566,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z567,z0,z2,z3,z4,z5,z6]),(0,[z222,z0,z2,z3,z4,z5,z6]),(0,[z0,z146,z2,z3,z4,z5,z568])],[(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z0,z570,z2,z3,z4,z5,z6]),(0,[z0,z571,z2,z3,z4,z5,z6]),(0,[z0,z2,z47,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z572,z6]),(0,[z0,z2,z3,z573,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z574,z6]),(0,[z0,z230,z3,z29,z4,z5,z6]),(0,[z0,z2,z541,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z575,z5,z6]),(0,[z0,z576,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z164,z6,z10]),(0,[z0,z2,z3,z4,z5,z6,z168])],[(0,[z0,z2,z3,z4,z63,z107,z6]),(0,[z0,z2,z3,z577,z4,z5,z6]),(0,[z0,z2,z578,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z579,z5,z6])],[(0,[z109,z0,z2,z3,z53,z5,z6])],[(0,[z0,z2,z16,z25,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z330]),(0,[z0,z157,z2,z3,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z580,z6]),(0,[z0,z2,z3,z4,z5,z132,z168])],[(0,[z0,z2,z3,z4,z5,z581,z6]),(0,[z0,z2,z3,z4,z582,z5,z6]),(1,[z20,z0,z2,z4,z5,z132]),(0,[z0,z2,z3,z4,z59,z5,z509])],[(0,[z0,z2,z3,z432,z4,z5,z6])]],
   [[(0,[z0,z2,z75,z3,z9,z4,z5]),(0,[z583,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z584,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z184])],[(0,[z0,z585,z2,z3,z4,z5,z6]),(0,[z586,z0,z2,z3,z4,z5,z6]),(0,[z0,z130,z16,z3,z4,z5,z6]),(0,[z587,z0,z2,z3,z4,z5,z6]),(0,[z0,z157,z2,z3,z4,z5,z6]),(0,[z0,z2,z140,z3,z4,z17,z5])],[(0,[z77,z0,z2,z3,z4,z5,z588]),(0,[z92,z0,z2,z3,z4,z5,z95]),(0,[z0,z2,z3,z4,z5,z95,z6]),(0,[z0,z2,z589,z3,z4,z5,z6]),(0,[z2,z3,z562,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z590,z6]),(0,[z0,z2,z3,z591,z4,z5,z6]),(1,[z0,z35,z2,z3,z9,z5])],[(0,[z0,z2,z3,z4,z82,z5,z6]),(0,[z0,z2,z3,z4,z592,z5,z6])],[(0,[z0,z593,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z594,z4,z5,z6]),(0,[z0,z595,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z596,z6]),(0,[z0,z597,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z562,z4,z5,z6]),(0,[z0,z2,z3,z4,z598,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z599]),(0,[z0,z2,z3,z600,z4,z5,z6]),(0,[z0,z547,z35,z2,z3,z4,z5]),(0,[z441,z0,z2,z3,z4,z5,z6]),(0,[z0,z601,z2,z3,z4,z5,z6])],[(0,[z602,z0,z2,z3,z4,z5,z6]),(0,[z123,z0,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z603,z4,z5,z6]),(0,[z0,z2,z138,z29,z4,z5,z6]),(0,[z604,z0,z2,z3,z4,z5,z6]),(0,[z0,z117,z3,z4,z105,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z322]),(0,[z101,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z605,z6])],[(0,[z81,z0,z245,z3,z4,z5,z6]),(1,[z0,z2,z3,z155,z5,z6]),(0,[z0,z35,z2,z3,z4,z105,z5]),(0,[z0,z2,z3,z4,z606,z5,z6])],[(0,[z81,z0,z2,z4,z74,z5,z6]),(0,[z109,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z192,z4,z5,z6])]],
   [[(0,[z14,z0,z2,z3,z4,z13,z6]),(0,[z0,z2,z3,z4,z5,z607,z6]),(0,[z0,z57,z2,z3,z4,z54,z5]),(0,[z0,z2,z3,z4,z5,z64,z111]),(0,[z0,z35,z608,z2,z3,z4,z5])],[(0,[z0,z609,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z36,z4,z5,z6]),(0,[z120,z0,z2,z3,z4,z54,z5]),(0,[z0,z610,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z132]),(1,[z0,z2,z3,z4,z5,z527])],[(0,[z65,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z611,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z107,z6]),(0,[z0,z612,z2,z3,z4,z5,z6]),(1,[z0,z157,z2,z17,z5,z6]),(0,[z0,z2,z3,z4,z5,z613,z6]),(0,[z614,z0,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z164])],[(1,[z0,z2,z3,z457,z5,z6]),(0,[z81,z0,z2,z3,z4,z5,z6]),(0,[z0,z273,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z615,z5,z6]),(0,[z0,z2,z138,z3,z4,z5,z449]),(0,[z616,z0,z2,z3,z4,z5,z6]),(0,[z0,z617,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z54,z5]),(0,[z0,z618,z2,z3,z4,z5,z6])],[(0,[z0,z2,z306,z4,z5,z45,z6]),(0,[z0,z2,z261,z3,z4,z63,z6]),(0,[z0,z2,z3,z619,z4,z5,z6]),(0,[z0,z2,z261,z3,z4,z5,z168])],[(0,[z0,z2,z3,z620,z4,z5,z6]),(1,[z0,z2,z541,z3,z4,z5])],[(0,[z621,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z74,z63,z6]),(0,[z0,z2,z3,z4,z5,z622,z6]),(0,[z0,z2,z3,z4,z5,z623,z6])],[(0,[z77,z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z423,z5,z6]),(0,[z0,z2,z3,z36,z5,z164,z6]),(0,[z0,z2,z3,z624,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z625,z6]),(0,[z0,z626,z2,z3,z4,z5,z6])]],
   [[(0,[z77,z0,z75,z3,z4,z5,z6]),(0,[z222,z0,z35,z2,z3,z4,z5]),(0,[z0,z627,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z484,z6]),(0,[z0,z2,z180,z3,z4,z5,z6])],[(0,[z628,z0,z2,z3,z4,z5,z6]),(0,[z0,z146,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z629,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z630,z6])],[(0,[z77,z2,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z631,z6]),(0,[z0,z2,z3,z4,z54,z5,z330]),(0,[z632,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z105,z5]),(0,[z0,z57,z2,z3,z4,z5,z132]),(0,[z0,z35,z2,z138,z3,z4,z5]),(0,[z0,z35,z2,z3,z4,z5,z64]),(0,[z0,z2,z3,z357,z9,z4,z5])],[(0,[z0,z2,z3,z633,z4,z5,z6]),(0,[z120,z0,z2,z3,z4,z5,z132]),(0,[z0,z2,z3,z4,z221,z5,z6])],[(0,[z0,z2,z634,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z359,z5,z6]),(0,[z0,z3,z4,z105,z5,z107,z6]),(0,[z0,z2,z3,z4,z5,z635,z6]),(0,[z0,z636,z2,z3,z4,z5,z6]),(0,[z0,z73,z2,z3,z4,z235,z6])],[(1,[z77,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z107])],[(0,[z0,z2,z3,z637,z4,z5,z6]),(0,[z0,z2,z3,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z237,z191,z6]),(0,[z0,z2,z3,z638,z4,z5,z6]),(0,[z639,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z164])],[(0,[z0,z640,z2,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z330]),(0,[z106,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z192,z4,z5,z6]),(0,[z0,z73,z2,z3,z44,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z641,z5,z6]),(0,[z642,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z643,z6]),(0,[z0,z2,z644,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z645,z6])],[(0,[z0,z117,z2,z3,z4,z107,z6])],[(0,[z0,z2,z3,z4,z5,z646,z6]),(0,[z0,z2,z647,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z189,z5,z6]),(1,[z0,z2,z3,z4,z5,z568]),(0,[z88,z0,z146,z2,z3,z4,z6])],[(0,[z0,z648,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z649]),(0,[z0,z2,z3,z4,z5,z322,z6])],[(0,[z88,z0,z2,z3,z50,z5,z6]),(0,[z0,z2,z3,z4,z650,z5,z6]),(0,[z0,z2,z3,z4,z651,z5,z6]),(0,[z0,z2,z502,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z68]),(0,[z0,z2,z3,z4,z652,z5,z6]),(0,[z0,z2,z261,z3,z9,z4,z5])],[(0,[z24,z0,z2,z3,z4,z5,z6]),(0,[z653,z0,z2,z3,z4,z5,z6]),(0,[z0,z654,z2,z3,z4,z5,z6]),(0,[z65,z2,z3,z4,z5,z143,z6]),(0,[z0,z2,z3,z655,z4,z5,z6]),(1,[z0,z35,z2,z3,z5,z10])],[(0,[z0,z2,z3,z4,z45,z235,z6]),(0,[z0,z2,z3,z4,z5,z568,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z588,z6]),(0,[z656,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z657,z5,z6]),(1,[z0,z230,z29,z4,z5,z6]),(0,[z0,z280,z2,z3,z4,z191,z6]),(0,[z0,z2,z3,z4,z5,z304,z6])],[(0,[z77,z0,z2,z3,z4,z5,z68]),(0,[z0,z2,z3,z4,z5,z658,z6]),(0,[z0,z35,z2,z3,z4,z59,z5])],[(0,[z0,z2,z3,z4,z659,z5,z6]),(0,[z0,z2,z3,z4,z660,z5,z6]),(0,[z88,z109,z0,z2,z3,z5,z6])],[(0,[z81,z0,z35,z2,z3,z4,z5]),(0,[z0,z35,z2,z3,z4,z50,z5]),(0,[z0,z2,z3,z4,z661,z5,z6]),(0,[z0,z2,z3,z4,z191,z5,z6])],[(0,[z662,z0,z2,z3,z4,z5,z6]),(0,[z20,z0,z2,z4,z5,z132,z6])],[(1,[z0,z2,z3,z4,z423,z6]),(0,[z521,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z663,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z302]),(0,[z0,z2,z3,z4,z664,z5,z6]),(0,[z0,z2,z3,z4,z5,z665,z6])],[(1,[z0,z2,z3,z4,z5,z588]),(0,[z0,z2,z666,z3,z4,z5,z6]),(0,[z81,z0,z2,z3,z4,z343,z6]),(0,[z0,z667,z2,z3,z4,z5,z6]),(0,[z668,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z561,z5,z6]),(0,[z0,z2,z3,z4,z669,z5,z6]),(0,[z109,z0,z2,z114,z4,z5,z6]),(0,[z0,z2,z670,z3,z4,z5,z6]),(1,[z0,z2,z138,z49,z5,z6]),(0,[z0,z2,z3,z4,z671,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z336]),(0,[z0,z2,z3,z4,z5,z672,z6])],[(0,[z673,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z674]),(1,[z0,z117,z3,z4,z105,z6]),(0,[z0,z2,z3,z44,z4,z322,z6])]],
   [[(0,[z675,z0,z2,z3,z4,z5,z6]),(0,[z81,z0,z2,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z676,z6]),(0,[z677,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z678,z3,z4,z5,z6]),(0,[z0,z2,z3,z679,z4,z5,z6])],[(0,[z0,z2,z680,z3,z4,z5,z6]),(1,[z0,z2,z247,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z184]),(0,[z0,z2,z3,z86,z4,z17,z5]),(0,[z0,z608,z2,z3,z4,z5,z6]),(0,[z681,z0,z2,z3,z4,z5,z6])],[(0,[z77,z0,z2,z3,z457,z5,z6]),(0,[z0,z682,z2,z3,z4,z5,z6]),(0,[z0,z73,z2,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z683])],[(0,[z0,z2,z25,z29,z4,z5,z6]),(0,[z0,z2,z684,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z199,z6]),(0,[z0,z2,z685,z3,z4,z5,z6]),(0,[z0,z2,z520,z3,z4,z5,z6])],[(0,[z0,z2,z3,z53,z50,z5,z6]),(0,[z0,z686,z2,z3,z4,z5,z6]),(0,[z362,z2,z3,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z477,z5,z6])],[(0,[z0,z2,z3,z4,z687,z5,z6]),(1,[z362,z2,z3,z4,z5,z6]),(0,[z0,z2,z688,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z689,z5,z6]),(0,[z0,z690,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z36,z59,z5,z6]),(0,[z0,z57,z2,z3,z4,z5,z111]),(0,[z0,z2,z3,z4,z5,z121,z168]),(1,[z0,z2,z3,z4,z533,z6])],[(0,[z0,z2,z3,z4,z5,z691,z6]),(0,[z692,z0,z2,z3,z4,z5,z6]),(0,[z88,z0,z73,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z304,z322])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z127]),(0,[z0,z2,z3,z4,z693,z5,z6])],[(0,[z0,z2,z3,z4,z694,z5,z6]),(0,[z0,z2,z695,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z696,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z6]),(0,[z697,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z302,z6]),(0,[z0,z2,z138,z3,z49,z5,z6]),(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z5,z111])],[(1,[z0,z2,z3,z104,z5,z6]),(0,[z2,z3,z4,z63,z5,z45,z6]),(0,[z0,z2,z3,z4,z5,z699,z6])],[(0,[z81,z28,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z50,z191,z5,z6]),(0,[z0,z2,z3,z4,z700,z5,z6]),(1,[z0,z2,z3,z9,z4,z5])],[(0,[z701,z0,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z330]),(0,[z88,z0,z52,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z702,z6]),(0,[z0,z2,z3,z4,z5,z45,z6]),(0,[z0,z703,z2,z3,z4,z5,z6])],[(0,[z24,z0,z35,z2,z3,z4,z5]),(0,[z14,z0,z2,z3,z36,z5,z6]),(1,[z0,z2,z4,z561,z5,z6]),(0,[z704,z0,z2,z3,z4,z5,z6]),(0,[z0,z654,z35,z2,z3,z4,z5]),(0,[z705,z0,z2,z3,z4,z5,z6])],[(0,[z88,z0,z2,z3,z4,z45,z6]),(0,[z0,z2,z3,z4,z533,z17,z6]),(0,[z0,z2,z706,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z77,z75,z3,z4,z342,z6]),(0,[z0,z245,z60,z4,z5,z6]),(0,[z81,z2,z25,z82,z5,z6]),(0,[z0,z130,z16,z4,z5,z6]),(0,[z0,z244,z2,z3,z5,z111])],[(0,[z0,z2,z3,z4,z5,z707]),(0,[z0,z2,z3,z708,z5,z6]),(0,[z77,z245,z3,z4,z5,z6]),(0,[z0,z709,z2,z3,z104,z5]),(0,[z0,z2,z3,z4,z710,z6]),(0,[z88,z0,z2,z3,z375,z6]),(0,[z0,z2,z546,z4,z5,z111]),(0,[z0,z2,z3,z9,z4,z388]),(0,[z2,z3,z4,z5,z711,z6]),(0,[z88,z0,z2,z282,z3,z322]),(0,[z0,z119,z608,z3,z4,z5]),(0,[z0,z244,z2,z261,z3,z168])],[(0,[z2,z3,z712,z4,z5,z6]),(0,[z0,z2,z3,z713,z5,z6]),(0,[z0,z2,z4,z5,z714,z6])],[(0,[z0,z28,z78,z4,z5,z6]),(0,[z77,z35,z75,z3,z4,z5]),(0,[z14,z2,z3,z36,z91,z6]),(0,[z0,z73,z2,z4,z715,z6])],[(0,[z0,z2,z4,z716,z5,z6]),(0,[z81,z103,z25,z4,z5,z6]),(0,[z14,z35,z2,z3,z36,z5]),(0,[z0,z2,z3,z4,z717,z6]),(0,[z0,z2,z3,z9,z241,z5]),(0,[z0,z2,z3,z4,z718,z6])],[(0,[z0,z35,z2,z3,z529,z5]),(0,[z0,z719,z3,z4,z5,z6]),(0,[z0,z2,z180,z140,z3,z4])],[(0,[z0,z2,z9,z4,z561,z5]),(0,[z66,z160,z2,z3,z4,z5]),(0,[z0,z2,z192,z4,z5,z6]),(0,[z2,z3,z4,z5,z720,z6])],[(0,[z0,z2,z3,z4,z5,z721]),(0,[z0,z2,z3,z7,z359,z5]),(0,[z120,z0,z3,z4,z5,z374]),(0,[z0,z35,z2,z3,z4,z722])]],
   [[(0,[z0,z2,z3,z4,z723,z6])],[(0,[z0,z2,z3,z4,z112,z68]),(0,[z0,z2,z3,z4,z5,z724]),(0,[z0,z709,z2,z3,z4,z5]),(0,[z0,z2,z306,z4,z235,z6]),(0,[z0,z2,z3,z4,z5,z725]),(0,[z88,z0,z517,z2,z3,z6]),(0,[z0,z2,z3,z4,z5,z568])],[(0,[z0,z2,z3,z359,z484,z6]),(0,[z0,z130,z16,z4,z5,z162]),(0,[z0,z2,z261,z3,z4,z270])],[(0,[z726,z0,z2,z3,z4,z5]),(0,[z0,z2,z180,z3,z4,z6])],[(0,[z0,z2,z3,z4,z727,z6]),(0,[z0,z2,z3,z4,z5,z728]),(0,[z0,z729,z2,z3,z5,z6]),(0,[z0,z2,z730,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z731]),(0,[z0,z57,z102,z3,z4,z5]),(0,[z88,z269,z35,z2,z3,z5])],[(0,[z0,z2,z3,z732,z5,z6]),(0,[z0,z35,z2,z3,z4,z112]),(0,[z123,z2,z3,z9,z50,z5]),(0,[z0,z35,z2,z3,z155,z5]),(0,[z0,z80,z2,z3,z9,z5]),(0,[z0,z35,z2,z3,z4,z237]),(0,[z0,z2,z502,z4,z5,z111])],[(0,[z0,z2,z394,z457,z5,z6]),(0,[z2,z3,z4,z5,z733,z330]),(0,[z0,z2,z3,z4,z5,z734]),(0,[z0,z2,z735,z3,z4,z5]),(0,[z0,z2,z3,z86,z4,z533]),(0,[z0,z35,z2,z3,z42,z5]),(0,[z0,z2,z3,z4,z736,z168])],[(0,[z0,z737,z3,z4,z5,z6]),(0,[z0,z245,z3,z4,z423,z6]),(0,[z0,z2,z3,z4,z5,z738]),(0,[z0,z230,z29,z4,z5,z6]),(0,[z0,z2,z3,z739,z4,z5]),(0,[z0,z2,z740,z3,z4,z5]),(0,[z0,z2,z3,z4,z741,z6])]],
   [[(0,[z642,z0,z3,z191,z5,z6]),(0,[z697,z0,z2,z4,z5,z132]),(0,[z742,z106,z0,z2,z3,z5])],[(0,[z0,z2,z3,z4,z342,z588]),(0,[z2,z737,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z423,z98]),(0,[z0,z269,z35,z2,z3,z5])],[(0,[z0,z2,z3,z4,z5,z743]),(0,[z0,z2,z3,z744,z4,z5]),(0,[z441,z2,z3,z4,z5,z330]),(0,[z0,z2,z3,z4,z5,z745])],[(0,[z0,z2,z746,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z747]),(0,[z0,z280,z2,z3,z36,z6]),(0,[z0,z2,z530,z4,z5,z111])],[(0,[z0,z2,z3,z4,z5,z748]),(0,[z0,z2,z3,z4,z423,z6]),(0,[z0,z2,z3,z4,z749,z6]),(0,[z0,z750,z3,z4,z5,z6]),(0,[z677,z2,z3,z36,z5,z6]),(0,[z0,z2,z3,z4,z5,z302]),(0,[z0,z2,z3,z9,z196,z5]),(0,[z751,z2,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z54,z216])],[(0,[z0,z35,z2,z3,z194,z5]),(0,[z0,z2,z3,z4,z5,z752]),(0,[z0,z2,z753,z3,z4,z5]),(0,[z88,z0,z2,z3,z425,z6]),(0,[z0,z2,z3,z4,z754,z6])],[(0,[z0,z2,z3,z755,z5,z6]),(0,[z402,z2,z3,z50,z5,z6]),(0,[z0,z146,z215,z3,z4,z6]),(0,[z0,z2,z3,z9,z4,z756])],[(0,[z0,z2,z78,z4,z5,z6]),(0,[z0,z35,z2,z3,z359,z5]),(0,[z109,z0,z280,z3,z191,z6]),(0,[z757,z35,z2,z3,z4,z5])]],
   [[(0,[z0,z2,z3,z758,z5,z6]),(0,[z65,z2,z3,z170,z4,z5]),(0,[z0,z2,z247,z4,z5,z6]),(0,[z0,z2,z3,z759,z5,z6])],[(0,[z0,z2,z3,z4,z5,z760]),(0,[z0,z2,z261,z3,z4,z317]),(0,[z0,z280,z52,z2,z3,z6]),(0,[z0,z761,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z762]),(1,[z0,z2,z763,z5,z6])],[(0,[z0,z2,z3,z4,z764,z6]),(0,[z0,z2,z765,z4,z5,z6]),(0,[z0,z2,z306,z4,z74,z6]),(0,[z92,z2,z3,z4,z766,z6]),(0,[z0,z35,z2,z767,z4,z5]),(0,[z521,z2,z3,z170,z4,z5])],[(0,[z0,z2,z3,z350,z59,z6]),(0,[z0,z2,z3,z4,z5,z768]),(0,[z0,z2,z3,z4,z5,z769]),(0,[z0,z2,z4,z5,z132,z714])],[(0,[z0,z245,z4,z74,z5,z6]),(0,[z0,z35,z2,z3,z4,z343]),(0,[z0,z2,z770,z4,z5,z6]),(0,[z0,z2,z3,z4,z771,z6]),(0,[z0,z35,z2,z138,z49,z5]),(0,[z0,z35,z187,z2,z3,z5]),(0,[z0,z2,z3,z772,z5,z6]),(0,[z20,z0,z2,z4,z5,z714]),(0,[z0,z2,z520,z4,z5,z132])],[(0,[z0,z2,z3,z4,z5,z773]),(0,[z0,z2,z3,z4,z533,z6]),(0,[z0,z35,z2,z173,z3,z5])],[(1,[z737,z3,z4,z5,z6]),(0,[z28,z60,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z774]),(0,[z0,z775,z3,z4,z5,z6]),(0,[z0,z2,z3,z104,z5,z98]),(0,[z0,z2,z3,z776,z5,z6]),(0,[z109,z0,z215,z3,z5,z6])],[(0,[z0,z103,z3,z104,z5,z6]),(0,[z0,z2,z3,z4,z13,z217]),(0,[z0,z2,z3,z9,z93,z5]),(0,[z0,z2,z3,z777,z5,z6]),(0,[z0,z2,z778,z4,z5,z6])]],
   [[(0,[z0,z103,z3,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z779]),(1,[z269,z35,z2,z3,z5])],[(0,[z0,z2,z3,z780,z5,z6]),(0,[z0,z781,z2,z4,z5,z6]),(0,[z563,z28,z3,z4,z5,z6]),(0,[z0,z369,z29,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z484]),(0,[z0,z2,z3,z295,z5,z199]),(0,[z269,z2,z3,z5,z164,z6]),(0,[z0,z35,z2,z3,z5,z21]),(0,[z0,z35,z2,z3,z5,z782])],[(0,[z0,z2,z3,z9,z4,z5]),(0,[z0,z2,z78,z181,z5,z6]),(0,[z783,z0,z2,z3,z5,z6]),(0,[z0,z2,z712,z4,z5,z6]),(0,[z0,z2,z3,z4,z784,z6]),(0,[z0,z2,z306,z4,z5,z725]),(0,[z0,z2,z3,z189,z5,z95]),(0,[z785,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z9,z573,z5]),(0,[z269,z2,z3,z9,z4,z5]),(0,[z88,z27,z35,z2,z3,z5]),(0,[z0,z547,z2,z133,z4,z5])],[(0,[z0,z2,z3,z786,z4,z5]),(0,[z0,z2,z3,z4,z5,z787]),(0,[z0,z2,z3,z4,z788,z5])],[(0,[z0,z2,z789,z4,z5,z6]),(0,[z0,z3,z4,z5,z790,z6]),(0,[z14,z2,z3,z36,z5,z217]),(0,[z2,z3,z4,z766,z5,z6]),(0,[z0,z130,z16,z4,z5,z286]),(0,[z0,z2,z3,z4,z54,z233])],[(0,[z0,z2,z4,z791,z5,z6]),(0,[z0,z2,z3,z4,z5,z792]),(0,[z0,z2,z3,z4,z5,z793]),(0,[z0,z35,z2,z47,z4,z235])],[(0,[z0,z157,z2,z9,z17,z5])],[(0,[z0,z2,z3,z794,z5,z6]),(0,[z0,z2,z795,z4,z5,z6]),(0,[z92,z2,z3,z155,z63,z6]),(0,[z0,z2,z3,z796,z5,z6]),(0,[z0,z797,z2,z3,z5,z6]),(0,[z0,z798,z3,z4,z5,z6]),(0,[z0,z2,z799,z4,z5,z6])]],
   [[(0,[z0,z800,z2,z4,z5,z6]),(0,[z616,z2,z3,z4,z45,z6]),(0,[z0,z117,z3,z4,z801,z6])],[(0,[z0,z2,z394,z4,z5,z588]),(0,[z0,z2,z802,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z803]),(0,[z804,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z805]),(0,[z0,z2,z3,z4,z227,z64])],[(0,[z0,z571,z16,z4,z5,z6]),(0,[z0,z3,z53,z806,z5,z6]),(0,[z0,z146,z3,z4,z107,z568]),(0,[z0,z2,z3,z807,z4,z5]),(0,[z0,z808,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z5,z809]),(0,[z0,z35,z2,z3,z5,z683]),(0,[z148,z0,z2,z3,z4,z216])],[(0,[z0,z810,z2,z3,z181,z5]),(0,[z811,z2,z3,z4,z5,z6]),(0,[z0,z157,z2,z533,z17,z6]),(0,[z0,z2,z49,z763,z5,z6])],[(0,[z0,z35,z2,z3,z181,z5]),(0,[z0,z812,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z813]),(0,[z0,z2,z261,z3,z4,z356]),(0,[z0,z2,z3,z4,z295,z5])],[(0,[z0,z2,z3,z7,z4,z5]),(0,[z0,z2,z3,z50,z5,z509]),(0,[z0,z814,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z815,z6]),(0,[z0,z2,z3,z4,z5,z736])],[(0,[z0,z2,z3,z4,z816,z6]),(0,[z0,z2,z3,z817,z5,z6]),(0,[z0,z2,z3,z4,z818,z6]),(0,[z0,z819,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z820,z6]),(0,[z0,z2,z3,z4,z5,z304])],[(0,[z0,z2,z3,z821,z4,z5]),(0,[z24,z2,z4,z550,z5,z6]),(0,[z0,z2,z3,z4,z91,z15]),(0,[z0,z2,z3,z4,z5,z822]),(0,[z0,z2,z138,z49,z9,z5]),(0,[z0,z2,z3,z4,z54,z736])]],
   [[(0,[z823,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z824,z4,z5]),(0,[z0,z2,z3,z189,z5,z127]),(0,[z461,z2,z3,z4,z63,z6]),(0,[z0,z2,z3,z825,z5,z6]),(0,[z0,z2,z3,z4,z5,z714])],[(0,[z0,z2,z3,z826,z4,z5]),(0,[z0,z827,z3,z4,z5,z6]),(1,[z2,z712,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z91]),(0,[z0,z2,z3,z806,z5,z6])],[(0,[z40,z2,z60,z4,z5,z6]),(0,[z0,z2,z3,z4,z91,z6]),(0,[z0,z2,z3,z155,z45,z6]),(0,[z0,z2,z3,z44,z59,z6])],[(0,[z0,z2,z3,z828,z5,z6]),(0,[z0,z2,z180,z29,z4,z6]),(0,[z0,z2,z3,z4,z5,z829])],[(0,[z0,z2,z3,z4,z5,z68]),(0,[z272,z28,z3,z9,z4,z5]),(0,[z0,z830,z3,z4,z5,z6]),(0,[z106,z0,z117,z2,z3,z6])],[(0,[z272,z737,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z831]),(0,[z0,z2,z832,z4,z5,z6]),(0,[z0,z2,z3,z9,z5,z199])],[(0,[z0,z2,z394,z9,z4,z5]),(0,[z0,z2,z3,z4,z5,z833]),(0,[z14,z2,z3,z36,z5,z15]),(0,[z0,z2,z3,z4,z5,z834])],[(0,[z28,z737,z3,z4,z5,z6]),(0,[z0,z365,z2,z17,z5,z6]),(0,[z0,z2,z3,z4,z835,z6])]],
   [[(0,[z0,z2,z4,z5,z836,z6]),(0,[z0,z2,z3,z4,z837,z6]),(0,[z0,z2,z3,z4,z5,z782]),(0,[z0,z35,z2,z3,z5,z385])],[(0,[z0,z2,z3,z457,z342,z6]),(0,[z0,z2,z3,z838,z4,z5]),(0,[z0,z2,z3,z4,z5,z839]),(0,[z0,z2,z3,z4,z5,z840]),(0,[z14,z2,z3,z36,z5,z6])],[(0,[z0,z2,z841,z4,z5,z6]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z0,z2,z3,z4,z5,z843])],[(0,[z0,z245,z3,z4,z343,z6]),(0,[z0,z2,z3,z4,z844,z6]),(0,[z0,z845,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z846]),(0,[z109,z0,z3,z191,z5,z6]),(0,[z0,z2,z3,z4,z6,z847]),(0,[z0,z2,z3,z4,z5,z848])],[(0,[z0,z2,z4,z849,z5,z6]),(0,[z0,z2,z4,z74,z343,z6]),(0,[z0,z850,z2,z3,z5,z6]),(0,[z0,z2,z3,z851,z4,z5]),(0,[z0,z2,z3,z4,z5,z852])],[(0,[z0,z2,z3,z4,z112,z6]),(0,[z0,z2,z541,z3,z50,z5]),(0,[z0,z2,z3,z853,z4,z5]),(0,[z92,z35,z2,z3,z4,z63]),(0,[z0,z2,z3,z4,z484,z330]),(0,[z0,z2,z213,z9,z4,z5]),(1,[z0,z3,z806,z5,z6]),(0,[z0,z2,z3,z4,z5,z336]),(0,[z0,z35,z73,z2,z4,z74])],[(0,[z0,z2,z306,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z423]),(0,[z214,z2,z3,z36,z5,z6]),(0,[z0,z2,z3,z4,z854,z6]),(0,[z88,z0,z35,z2,z47,z3]),(0,[z0,z617,z2,z3,z9,z5])],[(0,[z0,z2,z3,z181,z5,z68])]],
   [[(0,[z0,z2,z3,z4,z343,z6]),(0,[z81,z2,z25,z4,z5,z316]),(0,[z0,z855,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z367,z5])],[(0,[z0,z856,z2,z3,z4,z6]),(0,[z705,z2,z3,z4,z45,z6]),(0,[z0,z2,z3,z5,z6,z857]),(0,[z0,z35,z2,z3,z229,z5]),(0,[z0,z2,z114,z4,z5,z6]),(0,[z0,z2,z3,z9,z5,z376])],[(0,[z0,z858,z2,z3,z4,z5]),(0,[z88,z0,z2,z3,z537,z6]),(0,[z0,z2,z859,z3,z4,z5]),(1,[z0,z814,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z860]),(0,[z0,z861,z2,z3,z4,z5]),(0,[z0,z2,z138,z49,z5,z449])],[(0,[z0,z862,z3,z4,z5,z6]),(0,[z0,z2,z226,z3,z4,z168]),(0,[z0,z2,z3,z4,z5,z863]),(0,[z0,z35,z2,z3,z209,z5]),(0,[z88,z0,z34,z2,z3,z6])],[(0,[z0,z2,z3,z5,z6,z864]),(0,[z0,z865,z2,z3,z4,z5]),(0,[z0,z2,z3,z59,z866,z6])],[(0,[z24,z2,z60,z9,z4,z5]),(0,[z88,z0,z35,z2,z3,z45]),(0,[z0,z2,z3,z44,z320,z6]),(0,[z0,z2,z140,z3,z4,z5])],[(0,[z0,z2,z3,z4,z867,z6]),(0,[z0,z2,z3,z9,z82,z5]),(0,[z0,z2,z868,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z869]),(0,[z870,z0,z2,z3,z4,z6]),(0,[z120,z0,z3,z4,z477,z5])],[(0,[z0,z2,z3,z4,z5,z127]),(0,[z0,z2,z3,z9,z5,z152]),(0,[z0,z2,z3,z4,z871,z6]),(0,[z109,z0,z3,z442,z191,z5]),(0,[z0,z146,z3,z4,z295,z107]),(0,[z0,z35,z2,z3,z44,z59]),(0,[z0,z35,z2,z3,z4,z854])]],
   [[(0,[z0,z2,z394,z4,z5,z68]),(0,[z0,z2,z3,z181,z112,z6]),(0,[z28,z245,z3,z4,z5,z6]),(0,[z2,z60,z712,z4,z5,z6]),(0,[z88,z2,z3,z50,z45,z6]),(0,[z0,z35,z2,z3,z660,z5]),(0,[z0,z35,z2,z306,z4,z5]),(0,[z0,z2,z261,z3,z4,z168])],[(0,[z0,z35,z2,z394,z4,z5]),(0,[z2,z60,z206,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z286]),(0,[z27,z35,z2,z3,z4,z5])],[(0,[z0,z2,z3,z872,z5,z6]),(0,[z0,z35,z2,z3,z189,z5]),(0,[z0,z2,z3,z9,z5,z164])],[(0,[z0,z2,z3,z4,z873,z6]),(0,[z0,z2,z3,z874,z5,z6]),(0,[z0,z244,z2,z3,z5,z6])],[(0,[z0,z2,z180,z3,z50,z6]),(0,[z0,z2,z3,z4,z5,z875]),(0,[z0,z2,z3,z4,z5,z876]),(0,[z0,z3,z4,z5,z877,z184]),(0,[z0,z290,z2,z3,z4,z221])],[(0,[z0,z2,z3,z36,z5,z217]),(0,[z0,z2,z3,z878,z5,z6]),(0,[z0,z2,z3,z5,z782,z10])],[(0,[z0,z2,z3,z4,z423,z316]),(0,[z0,z2,z3,z4,z766,z6]),(0,[z879,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z880,z4,z5])],[(0,[z0,z2,z3,z838,z457,z5]),(0,[z0,z2,z3,z4,z5,z881]),(0,[z0,z2,z882,z3,z4,z5]),(0,[z0,z2,z3,z59,z96,z6]),(0,[z0,z2,z3,z4,z5,z883]),(1,[z0,z2,z4,z5,z714]),(0,[z0,z2,z3,z44,z59,z509]),(0,[z0,z884,z3,z9,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z5,z885]),(0,[z0,z469,z29,z4,z5,z6]),(0,[z0,z2,z3,z5,z886,z6]),(0,[z0,z244,z2,z3,z5,z121])],[(0,[z0,z2,z394,z4,z112,z6]),(0,[z0,z2,z3,z82,z423,z6]),(0,[z0,z2,z3,z189,z5,z6]),(0,[z2,z3,z36,z887,z5,z6]),(0,[z269,z35,z2,z3,z5,z6]),(0,[z0,z35,z2,z888,z4,z5]),(0,[z0,z2,z3,z357,z4,z42])],[(0,[z2,z3,z4,z5,z143,z733]),(0,[z0,z2,z3,z5,z6,z889]),(0,[z0,z2,z418,z4,z5,z132]),(0,[z88,z0,z2,z3,z381,z6]),(0,[z0,z2,z282,z3,z4,z5])],[(0,[z77,z75,z3,z457,z5,z6]),(0,[z0,z35,z2,z3,z457,z5]),(0,[z0,z2,z3,z4,z5,z217]),(0,[z0,z35,z2,z3,z651,z5]),(0,[z0,z2,z3,z4,z722,z6])],[(0,[z0,z2,z3,z432,z93,z5]),(0,[z890,z2,z3,z9,z4,z5])],[(0,[z0,z2,z3,z4,z5,z891]),(0,[z81,z2,z78,z4,z5,z6]),(0,[z0,z103,z3,z4,z423,z6]),(0,[z0,z2,z3,z7,z5,z164]),(0,[z2,z3,z4,z13,z45,z6]),(0,[z451,z35,z2,z3,z36,z5]),(0,[z106,z0,z2,z3,z9,z5]),(0,[z0,z35,z2,z3,z5,z471]),(0,[z0,z2,z3,z4,z892,z6]),(0,[z0,z2,z3,z44,z866,z6])],[(0,[z0,z2,z78,z4,z342,z6]),(0,[z0,z2,z893,z4,z5,z6]),(0,[z0,z2,z3,z50,z13,z6])],[(0,[z66,z2,z3,z4,z5,z330]),(0,[z0,z2,z3,z4,z894,z6]),(0,[z109,z0,z114,z191,z5,z6]),(0,[z0,z94,z2,z3,z9,z5]),(0,[z0,z2,z4,z763,z5,z6]),(0,[z0,z2,z3,z9,z4,z895])]],
   [[(0,[z0,z2,z3,z896,z5,z6]),(0,[z897,z2,z3,z4,z5,z6])],[(0,[z0,z2,z306,z4,z343,z6]),(0,[z0,z2,z3,z898,z5,z6]),(0,[z65,z2,z3,z4,z5,z143]),(0,[z0,z2,z3,z899,z5,z6]),(0,[z0,z2,z3,z900,z4,z5]),(0,[z88,z0,z2,z3,z866,z6])],[(0,[z0,z2,z3,z4,z901,z6]),(0,[z0,z35,z2,z3,z694,z5]),(0,[z222,z2,z4,z561,z45,z6]),(0,[z2,z3,z562,z9,z4,z5]),(0,[z0,z2,z3,z902,z4,z5]),(0,[z751,z2,z3,z4,z5,z6])],[(0,[z0,z2,z903,z4,z5,z6]),(0,[z0,z2,z904,z3,z4,z5]),(0,[z0,z2,z3,z104,z5,z316]),(0,[z123,z2,z3,z7,z50,z5]),(0,[z2,z3,z155,z50,z5,z6]),(0,[z0,z2,z3,z155,z63,z6]),(0,[z0,z2,z3,z5,z6,z905]),(0,[z0,z2,z3,z4,z5,z906])],[(0,[z0,z2,z3,z442,z4,z237]),(0,[z0,z2,z3,z4,z907,z5]),(0,[z0,z2,z763,z17,z5,z6])],[(0,[z0,z35,z2,z3,z603,z5]),(1,[z2,z3,z4,z766,z6]),(0,[z0,z35,z2,z3,z255,z5]),(0,[z0,z908,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z909,z6]),(0,[z0,z35,z130,z16,z4,z5]),(0,[z0,z690,z16,z4,z5,z6]),(0,[z0,z2,z114,z4,z5,z910]),(0,[z88,z0,z2,z247,z4,z6])],[(0,[z0,z2,z3,z4,z911,z6]),(0,[z0,z2,z3,z4,z5,z912]),(0,[z0,z35,z2,z3,z4,z388]),(0,[z0,z2,z3,z4,z5,z84]),(0,[z106,z0,z146,z3,z107,z6]),(0,[z0,z2,z3,z4,z913,z6])]],
   [[(0,[z0,z2,z3,z4,z914,z6]),(0,[z0,z245,z3,z4,z5,z98]),(0,[z81,z2,z712,z4,z5,z6]),(0,[z0,z2,z3,z4,z91,z217]),(0,[z0,z915,z2,z3,z4,z5]),(0,[z916,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z917,z5,z6]),(0,[z28,z3,z361,z4,z5,z6]),(0,[z2,z3,z4,z766,z45,z6]),(0,[z0,z2,z3,z918,z5,z6])],[(0,[z0,z2,z3,z4,z919,z6]),(0,[z0,z2,z3,z9,z4,z13]),(0,[z0,z2,z306,z4,z5,z920]),(0,[z0,z2,z921,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z327])],[(0,[z0,z245,z3,z4,z5,z6]),(0,[z14,z2,z3,z9,z36,z5]),(0,[z0,z2,z3,z4,z5,z922]),(0,[z0,z2,z47,z4,z235,z336]),(0,[z88,z27,z2,z3,z322,z6]),(0,[z0,z11,z3,z232,z4,z5])],[(0,[z0,z923,z3,z4,z5,z6]),(0,[z0,z924,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z6,z925]),(0,[z88,z0,z2,z3,z183,z6]),(0,[z0,z2,z3,z926,z5,z6])],[(0,[z0,z2,z3,z4,z5,z98]),(0,[z0,z2,z3,z4,z5,z15]),(0,[z0,z2,z3,z5,z927,z6]),(0,[z0,z157,z2,z140,z17,z5]),(0,[z0,z2,z264,z3,z4,z168])],[(0,[z0,z2,z541,z3,z36,z5]),(0,[z0,z2,z3,z4,z5,z928])],[(0,[z0,z2,z3,z4,z5,z929]),(0,[z171,z2,z3,z4,z45,z6]),(0,[z0,z35,z280,z2,z3,z4]),(0,[z0,z35,z2,z3,z5,z210])]],
   [[(0,[z0,z2,z3,z4,z5,z6]),(0,[z269,z2,z3,z4,z5,z6]),(0,[z0,z274,z2,z4,z74,z6])],[(0,[z0,z2,z3,z4,z930,z6]),(0,[z0,z2,z3,z931,z5,z6]),(0,[z0,z35,z2,z192,z4,z5])],[(0,[z737,z75,z3,z4,z5,z6]),(0,[z0,z932,z3,z4,z5,z6]),(0,[z0,z933,z3,z4,z5,z6]),(0,[z0,z2,z261,z3,z4,z504]),(0,[z0,z2,z3,z934,z4,z5]),(0,[z0,z2,z47,z4,z715,z6]),(0,[z0,z35,z2,z3,z5,z218])],[(0,[z0,z2,z3,z4,z935,z5]),(0,[z222,z2,z3,z9,z4,z45]),(0,[z92,z2,z3,z4,z63,z95]),(0,[z2,z3,z4,z63,z766,z6]),(0,[z108,z2,z3,z4,z5,z330]),(0,[z88,z0,z2,z3,z122,z6])],[(0,[z0,z2,z936,z4,z5,z6]),(0,[z0,z2,z3,z937,z4,z5]),(0,[z0,z2,z3,z9,z155,z5]),(0,[z0,z3,z4,z806,z5,z6]),(0,[z0,z11,z3,z4,z5,z184]),(0,[z0,z938,z3,z4,z5,z6]),(0,[z0,z2,z3,z939,z5,z6])],[(0,[z0,z2,z940,z4,z5,z6]),(0,[z0,z915,z2,z3,z189,z5]),(1,[z0,z2,z3,z866,z6])],[(0,[z77,z75,z3,z4,z5,z588]),(0,[z0,z2,z3,z941,z4,z5]),(0,[z0,z273,z2,z3,z4,z5]),(0,[z0,z942,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z943]),(0,[z944,z2,z3,z4,z5,z6])],[(0,[z81,z2,z25,z4,z423,z6]),(0,[z0,z2,z3,z4,z945,z6]),(0,[z0,z35,z2,z3,z575,z5])]],
   [[(0,[z0,z2,z3,z946,z5,z6]),(0,[z0,z2,z3,z4,z5,z947]),(0,[z0,z35,z2,z3,z486,z5]),(0,[z0,z35,z2,z114,z4,z5])],[(0,[z0,z948,z2,z3,z4,z5]),(0,[z123,z2,z3,z887,z5,z6]),(0,[z109,z0,z3,z237,z191,z6]),(0,[z0,z2,z3,z4,z5,z949]),(0,[z0,z117,z192,z4,z105,z6]),(0,[z0,z2,z3,z9,z4,z533])],[(0,[z0,z2,z3,z4,z950,z6]),(0,[z0,z2,z3,z4,z5,z162]),(0,[z0,z2,z3,z4,z5,z951]),(0,[z0,z73,z2,z9,z4,z74])],[(0,[z0,z2,z3,z181,z5,z6]),(0,[z0,z2,z3,z4,z342,z68]),(0,[z0,z2,z3,z359,z5,z6]),(0,[z0,z230,z814,z4,z5,z6]),(0,[z0,z35,z262,z2,z3,z5]),(0,[z0,z2,z952,z4,z5,z6])],[(0,[z0,z2,z3,z4,z953,z6]),(0,[z0,z2,z3,z4,z5,z954])],[(0,[z165,z2,z3,z50,z5,z6]),(0,[z0,z2,z180,z3,z36,z6])],[(0,[z0,z2,z3,z955,z5,z6]),(0,[z362,z2,z60,z4,z5,z6]),(0,[z0,z2,z956,z4,z5,z6]),(0,[z0,z2,z3,z4,z45,z95]),(0,[z362,z2,z3,z4,z5,z957]),(0,[z958,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z959,z5,z6]),(0,[z362,z2,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z960,z5]),(0,[z88,z0,z2,z3,z493,z6]),(0,[z88,z0,z2,z3,z9,z322])]],
   [[(0,[z0,z2,z3,z4,z5,z961]),(0,[z0,z35,z2,z3,z104,z5]),(0,[z0,z2,z3,z4,z962,z6]),(0,[z106,z0,z2,z3,z45,z6]),(0,[z0,z2,z3,z294,z4,z63]),(0,[z66,z2,z3,z4,z5,z733]),(0,[z505,z0,z3,z4,z5,z121]),(0,[z0,z73,z2,z4,z700,z6]),(0,[z88,z0,z2,z3,z322,z6]),(0,[z916,z35,z2,z3,z4,z5]),(0,[z0,z35,z2,z963,z4,z5])],[(0,[z0,z2,z814,z4,z5,z6]),(0,[z0,z2,z3,z5,z964,z6])],[(0,[z272,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z965]),(0,[z0,z2,z3,z4,z966,z6]),(0,[z0,z2,z3,z4,z5,z967])],[(0,[z77,z75,z3,z9,z4,z5]),(0,[z0,z2,z3,z9,z4,z343]),(0,[z0,z2,z3,z4,z968,z6]),(0,[z27,z2,z3,z155,z5,z6]),(0,[z0,z2,z3,z93,z5,z143]),(0,[z0,z2,z3,z4,z5,z969]),(0,[z0,z2,z3,z4,z5,z970]),(0,[z0,z2,z3,z5,z6,z971]),(0,[z0,z73,z2,z4,z74,z6])],[(0,[z0,z2,z394,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z972]),(0,[z81,z2,z25,z104,z5,z6]),(0,[z362,z2,z3,z973,z5,z6]),(0,[z0,z2,z3,z4,z5,z974]),(0,[z0,z2,z3,z4,z975,z6]),(0,[z0,z2,z767,z4,z5,z6]),(0,[z0,z35,z2,z976,z4,z5])],[(0,[z0,z2,z3,z4,z977,z5]),(0,[z0,z2,z3,z82,z343,z6]),(0,[z81,z2,z25,z9,z4,z5]),(0,[z0,z35,z2,z3,z93,z5]),(0,[z0,z2,z978,z3,z4,z6]),(0,[z106,z0,z2,z3,z294,z5]),(0,[z0,z2,z192,z9,z4,z5]),(0,[z0,z35,z2,z3,z297,z5]),(0,[z88,z0,z35,z117,z2,z3]),(0,[z148,z0,z35,z2,z3,z5])],[(0,[z0,z2,z979,z4,z5,z6]),(0,[z0,z2,z3,z980,z4,z5]),(0,[z0,z2,z976,z4,z5,z6]),(0,[z0,z35,z2,z180,z3,z4])],[(0,[z0,z810,z2,z3,z4,z5]),(0,[z0,z2,z3,z981,z5,z6]),(0,[z0,z2,z4,z5,z982,z6]),(0,[z0,z2,z3,z36,z5,z509]),(0,[z35,z2,z3,z562,z4,z5]),(0,[z0,z2,z3,z4,z5,z983]),(0,[z0,z2,z984,z3,z4,z5]),(0,[z0,z2,z3,z44,z59,z527]),(0,[z0,z2,z985,z4,z5,z6])]],
   [[(0,[z0,z35,z2,z3,z4,z5]),(0,[z2,z60,z78,z4,z5,z6]),(0,[z0,z245,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z343,z98]),(0,[z0,z35,z2,z4,z561,z5]),(0,[z362,z230,z29,z4,z5,z6]),(0,[z0,z814,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z237,z6]),(0,[z0,z3,z4,z801,z107,z6]),(0,[z0,z2,z3,z4,z986,z5]),(0,[z0,z198,z3,z4,z5,z121]),(0,[z0,z987,z2,z3,z4,z5]),(0,[z269,z35,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z988]),(0,[z0,z2,z3,z5,z6,z782])],[(0,[z0,z103,z3,z4,z343,z6]),(0,[z0,z989,z2,z3,z4,z5]),(0,[z0,z57,z3,z4,z5,z184])],[(0,[z0,z2,z3,z4,z5,z990]),(0,[z24,z35,z2,z60,z4,z5]),(0,[z0,z2,z3,z4,z5,z991]),(0,[z0,z3,z806,z191,z5,z6]),(0,[z0,z2,z3,z992,z4,z5]),(0,[z0,z35,z2,z3,z170,z5])],[(0,[z0,z2,z3,z993,z5,z6]),(0,[z0,z2,z3,z155,z5,z95]),(0,[z0,z2,z213,z4,z5,z6]),(0,[z994,z2,z3,z4,z5,z6]),(0,[z0,z117,z247,z4,z105,z6])],[(0,[z0,z2,z995,z4,z5,z6]),(0,[z0,z2,z3,z887,z5,z6]),(0,[z0,z2,z3,z4,z5,z733]),(0,[z0,z2,z3,z4,z996,z5]),(0,[z0,z2,z997,z4,z5,z6]),(0,[z0,z2,z3,z998,z5,z6]),(0,[z0,z2,z3,z9,z260,z5]),(0,[z0,z2,z110,z4,z5,z111]),(0,[z0,z2,z3,z4,z42,z168])],[(0,[z0,z999,z2,z3,z4,z5]),(0,[z0,z421,z2,z4,z74,z6]),(0,[z0,z2,z180,z16,z4,z6]),(0,[z0,z2,z3,z4,z5,z910]),(0,[z0,z2,z3,z4,z5,z335]),(0,[z0,z35,z2,z795,z4,z5]),(0,[z0,z2,z261,z3,z385,z168])],[(0,[z0,z2,z3,z1000,z5,z6]),(0,[z0,z2,z3,z4,z1001,z6]),(0,[z0,z2,z4,z74,z646,z6]),(0,[z0,z2,z3,z4,z5,z1002]),(0,[z0,z2,z3,z4,z756,z6]),(0,[z0,z2,z140,z3,z50,z5]),(0,[z0,z230,z29,z9,z4,z5]),(0,[z0,z57,z3,z4,z5,z877]),(0,[z0,z1003,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z54,z64]),(0,[z0,z2,z3,z4,z6,z736])],[(0,[z0,z2,z394,z181,z5,z6]),(0,[z0,z2,z3,z1004,z181,z5]),(0,[z0,z948,z2,z3,z457,z5]),(0,[z0,z2,z3,z4,z1005,z6]),(0,[z0,z2,z3,z1006,z4,z5]),(0,[z0,z2,z1007,z4,z5,z6]),(0,[z0,z648,z3,z4,z5,z184]),(0,[z0,z2,z3,z1008,z5,z6]),(0,[z0,z2,z3,z294,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z5,z1009]),(0,[z0,z2,z1010,z4,z5,z6]),(0,[z0,z35,z2,z3,z7,z5]),(0,[z681,z2,z3,z4,z63,z6]),(0,[z0,z2,z247,z4,z5,z1011]),(0,[z0,z2,z3,z1012,z4,z5])],[(0,[z0,z2,z3,z4,z895,z6]),(0,[z0,z35,z2,z3,z5,z319]),(0,[z222,z2,z3,z4,z766,z6]),(0,[z0,z2,z1013,z4,z5,z6]),(0,[z0,z2,z541,z3,z4,z237]),(0,[z0,z146,z3,z4,z107,z6]),(0,[z0,z2,z3,z4,z5,z1014])],[(0,[z0,z2,z3,z104,z423,z6]),(0,[z451,z2,z3,z36,z5,z6]),(0,[z65,z2,z3,z4,z388,z143]),(0,[z2,z3,z4,z5,z1015,z6]),(0,[z0,z2,z3,z5,z199,z6])],[(0,[z0,z2,z3,z1016,z5,z6]),(0,[z0,z2,z3,z9,z181,z5]),(0,[z24,z2,z60,z4,z5,z6]),(0,[z88,z0,z273,z2,z3,z5]),(0,[z0,z2,z3,z4,z5,z1017]),(0,[z0,z16,z814,z4,z5,z6]),(0,[z0,z291,z3,z4,z5,z184])],[(0,[z0,z2,z3,z1018,z5,z6]),(0,[z0,z2,z3,z4,z1019,z6]),(0,[z0,z2,z3,z4,z5,z920]),(0,[z0,z2,z47,z4,z26,z6]),(0,[z0,z2,z3,z442,z4,z5]),(0,[z88,z0,z2,z3,z304,z322])],[(0,[z77,z75,z3,z4,z5,z68]),(0,[z92,z35,z2,z3,z50,z5]),(0,[z2,z3,z4,z5,z733,z6]),(0,[z230,z562,z29,z4,z5,z6]),(0,[z0,z262,z2,z17,z5,z6]),(0,[z0,z2,z1020,z3,z4,z5]),(1,[z0,z2,z3,z4,z736])],[(0,[z0,z2,z3,z4,z1021,z6]),(0,[z0,z1022,z2,z3,z4,z5]),(0,[z65,z2,z3,z93,z5,z143]),(0,[z0,z52,z3,z53,z5,z302]),(0,[z0,z2,z47,z4,z235,z6]),(0,[z958,z35,z2,z3,z4,z5])],[(0,[z250,z2,z3,z50,z5,z6]),(0,[z0,z35,z2,z3,z4,z91]),(0,[z0,z2,z496,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z1023]),(0,[z0,z2,z3,z4,z5,z1024]),(0,[z0,z157,z2,z763,z5,z6])]],
   [[(0,[z0,z2,z3,z9,z4,z342]),(0,[z0,z35,z2,z3,z5,z373]),(0,[z0,z2,z180,z3,z86,z4]),(0,[z88,z269,z2,z3,z322,z6])],[(0,[z0,z2,z1025,z3,z4,z6]),(0,[z0,z1026,z2,z3,z4,z5]),(0,[z0,z35,z2,z3,z638,z5]),(0,[z0,z2,z282,z3,z59,z5]),(0,[z0,z2,z261,z3,z4,z381])],[(0,[z0,z2,z3,z941,z82,z5]),(0,[z35,z2,z3,z50,z5,z45]),(0,[z0,z146,z3,z4,z801,z6]),(0,[z0,z2,z3,z4,z5,z1027])],[(1,[z2,z3,z887,z5,z6]),(1,[z2,z3,z4,z5,z733]),(0,[z362,z2,z3,z9,z4,z5]),(0,[z1028,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z5,z199])],[(0,[z362,z75,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1029]),(0,[z0,z35,z103,z3,z4,z5]),(0,[z0,z2,z3,z4,z1030,z6]),(0,[z0,z2,z3,z4,z6,z1031]),(0,[z0,z2,z140,z3,z4,z533])],[(0,[z0,z2,z3,z4,z5,z1032]),(0,[z0,z2,z3,z4,z5,z449]),(0,[z0,z884,z3,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z1033]),(0,[z0,z2,z3,z9,z372,z5])],[(0,[z77,z75,z3,z4,z112,z6]),(0,[z0,z2,z3,z4,z5,z1034]),(0,[z27,z2,z3,z50,z5,z6]),(0,[z362,z2,z3,z4,z5,z793])],[(0,[z0,z1035,z2,z3,z4,z6]),(0,[z0,z2,z3,z1036,z5,z6]),(0,[z0,z516,z3,z4,z107,z6]),(0,[z65,z2,z3,z4,z5,z733]),(0,[z1037,z2,z3,z4,z5,z6]),(0,[z0,z2,z1038,z4,z5,z6]),(0,[z0,z1039,z3,z4,z5,z6]),(0,[z0,z2,z110,z4,z5,z714]),(0,[z88,z0,z35,z2,z3,z59]),(0,[z0,z2,z3,z5,z6,z385]),(0,[z0,z244,z2,z3,z54,z5])]],
   [[],[(0,[z0,z2,z3,z4,z1040,z6]),(0,[z81,z2,z351,z4,z5,z6]),(0,[z0,z2,z3,z4,z388,z6]),(0,[z109,z0,z213,z191,z5,z6]),(0,[z0,z2,z3,z4,z5,z391])],[(0,[z0,z1041,z3,z4,z5,z6]),(0,[z0,z3,z4,z1042,z5,z6]),(0,[z0,z3,z4,z5,z6,z1043]),(0,[z109,z0,z3,z9,z191,z5]),(0,[z0,z2,z3,z4,z5,z1044]),(0,[z0,z2,z3,z294,z5,z199]),(0,[z0,z2,z3,z4,z5,z1045]),(0,[z890,z2,z3,z4,z5,z6]),(0,[z0,z35,z244,z2,z3,z5]),(0,[z0,z2,z3,z59,z6,z125])],[(0,[z0,z2,z3,z4,z1046,z6]),(0,[z0,z1047,z3,z4,z5,z6]),(0,[z0,z2,z3,z1048,z5,z6]),(0,[z0,z2,z963,z4,z5,z6])],[(0,[z0,z1049,z2,z3,z4,z5]),(0,[z123,z273,z2,z3,z50,z5]),(0,[z92,z2,z3,z9,z4,z63]),(0,[z2,z3,z4,z1050,z5,z6]),(0,[z1051,z2,z3,z4,z5,z6]),(0,[z88,z0,z35,z2,z3,z381])],[(0,[z0,z245,z3,z4,z5,z316]),(0,[z0,z1052,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1053]),(0,[z0,z2,z3,z93,z5,z6]),(0,[z0,z35,z2,z3,z410,z5])],[(0,[z0,z2,z3,z1054,z4,z5]),(0,[z0,z2,z3,z4,z5,z1055]),(0,[z0,z2,z3,z4,z1056,z6]),(0,[z14,z2,z3,z887,z5,z6]),(0,[z0,z35,z146,z3,z4,z107]),(0,[z0,z2,z180,z3,z9,z4]),(0,[z0,z2,z3,z4,z5,z1057]),(0,[z0,z2,z3,z5,z866,z6])],[(0,[z0,z35,z2,z3,z696,z5]),(0,[z0,z2,z3,z4,z63,z95]),(0,[z0,z3,z4,z5,z877,z6]),(0,[z0,z1058,z2,z3,z4,z5])]],
   [[(0,[z2,z3,z562,z4,z5,z6]),(0,[z0,z245,z3,z82,z5,z6]),(0,[z742,z0,z2,z3,z4,z5]),(0,[z0,z35,z157,z2,z17,z5]),(0,[z20,z0,z2,z4,z352,z5]),(0,[z0,z2,z1059,z9,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1060]),(0,[z106,z0,z2,z3,z63,z6]),(0,[z0,z2,z3,z4,z5,z1061]),(0,[z0,z2,z3,z1062,z4,z5]),(0,[z106,z0,z146,z2,z3,z6]),(0,[z0,z2,z3,z4,z1063,z6]),(0,[z0,z2,z398,z4,z5,z111]),(0,[z0,z244,z2,z3,z5,z132])],[(0,[z0,z2,z3,z4,z5,z316]),(0,[z0,z2,z3,z82,z5,z98]),(0,[z0,z2,z3,z4,z5,z1064]),(0,[z0,z146,z3,z294,z4,z107]),(0,[z0,z2,z3,z1065,z4,z5]),(0,[z0,z244,z2,z261,z3,z5])],[(0,[z0,z538,z29,z4,z5,z6]),(0,[z2,z3,z4,z1066,z5,z6]),(0,[z0,z52,z3,z9,z53,z5]),(0,[z0,z2,z247,z44,z4,z6])],[(0,[z0,z35,z2,z3,z82,z5]),(0,[z0,z2,z3,z359,z388,z6]),(0,[z0,z35,z2,z3,z511,z5])],[(0,[z0,z2,z3,z82,z5,z6]),(0,[z81,z35,z2,z25,z4,z5]),(0,[z0,z2,z3,z4,z5,z1067]),(0,[z0,z2,z4,z1068,z5,z6]),(0,[z1069,z2,z3,z4,z5,z6]),(0,[z0,z2,z1070,z4,z5,z6]),(0,[z0,z57,z3,z4,z5,z580]),(0,[z0,z2,z3,z9,z5,z403])],[(0,[z0,z2,z3,z4,z5,z1071]),(0,[z0,z103,z3,z4,z5,z98]),(0,[z0,z2,z1072,z4,z5,z6]),(0,[z0,z2,z3,z4,z1073,z6]),(0,[z0,z2,z390,z4,z5,z132]),(0,[z27,z2,z3,z4,z5,z1045]),(0,[z0,z2,z3,z9,z44,z59])],[(0,[z0,z2,z3,z4,z342,z6]),(0,[z0,z2,z3,z457,z5,z588]),(0,[z0,z2,z3,z1074,z4,z5]),(0,[z0,z2,z3,z4,z1075,z6]),(0,[z65,z2,z3,z359,z5,z143]),(0,[z0,z2,z261,z3,z4,z736])]],
   [[(0,[z24,z2,z712,z4,z5,z6]),(0,[z0,z2,z3,z4,z54,z309]),(0,[z0,z244,z2,z3,z9,z5])],[(0,[z0,z103,z3,z4,z5,z6]),(0,[z0,z2,z78,z457,z5,z6]),(0,[z0,z2,z3,z4,z5,z1076]),(0,[z0,z2,z3,z4,z1077,z6]),(0,[z0,z280,z2,z3,z4,z6]),(0,[z0,z2,z3,z59,z5,z302]),(0,[z0,z2,z3,z4,z6,z1078])],[(0,[z2,z3,z887,z50,z5,z6]),(0,[z120,z0,z3,z4,z5,z877]),(0,[z20,z0,z2,z4,z5,z132]),(0,[z0,z1079,z2,z3,z4,z5])],[(0,[z0,z2,z1080,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1081]),(0,[z0,z2,z3,z4,z5,z1082])],[(0,[z0,z157,z2,z180,z17,z6])],[(0,[z77,z737,z3,z4,z5,z6]),(0,[z0,z273,z2,z3,z59,z5]),(0,[z0,z130,z814,z4,z5,z6]),(0,[z0,z1083,z2,z3,z4,z5]),(0,[z0,z1084,z2,z3,z4,z5])],[(0,[z123,z35,z2,z3,z50,z5]),(0,[z0,z2,z3,z1085,z5,z6]),(0,[z0,z2,z1086,z3,z4,z5]),(0,[z211,z160,z2,z3,z4,z5]),(0,[z0,z35,z2,z3,z9,z5])],[(0,[z0,z2,z3,z4,z1087,z6]),(0,[z0,z2,z3,z9,z4,z112]),(0,[z0,z2,z140,z3,z36,z5]),(0,[z0,z2,z3,z9,z4,z237]),(0,[z0,z2,z1088,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z1089]),(0,[z0,z2,z3,z4,z866,z6])]],
   [[(0,[z0,z2,z3,z786,z155,z5]),(0,[z0,z1090,z3,z4,z5,z6])],[(0,[z27,z2,z3,z4,z45,z6]),(0,[z0,z2,z3,z1091,z5,z6]),(0,[z451,z2,z3,z4,z5,z143]),(0,[z0,z280,z2,z541,z3,z4]),(0,[z0,z2,z3,z4,z1092,z6]),(0,[z0,z2,z3,z5,z164,z527])],[(0,[z0,z2,z3,z181,z342,z6]),(0,[z0,z2,z3,z4,z1093,z6]),(0,[z0,z2,z3,z1094,z4,z5]),(0,[z0,z2,z3,z155,z5,z6]),(0,[z1095,z2,z3,z4,z5,z6])],[(0,[z77,z75,z78,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1096]),(0,[z0,z1097,z2,z3,z4,z5]),(0,[z0,z2,z3,z1098,z5,z6]),(0,[z0,z2,z3,z4,z5,z1099]),(1,[z0,z2,z3,z5,z782])],[(0,[z0,z2,z3,z1100,z5,z6]),(0,[z0,z35,z2,z3,z51,z5]),(0,[z0,z35,z2,z3,z4,z741])],[(0,[z0,z1101,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z527])],[(0,[z0,z2,z3,z4,z5,z1102]),(0,[z222,z2,z306,z4,z45,z6]),(0,[z362,z2,z3,z713,z5,z6]),(0,[z0,z2,z1103,z3,z4,z6]),(0,[z0,z57,z3,z324,z4,z5]),(0,[z0,z157,z2,z17,z5,z6])],[(0,[z0,z1104,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z292,z64]),(0,[z109,z0,z541,z3,z191,z5]),(0,[z0,z2,z4,z5,z714,z111])]],
   [[(0,[z0,z2,z3,z1105,z5,z6]),(0,[z0,z2,z3,z50,z5,z217]),(0,[z362,z2,z3,z4,z871,z6]),(0,[z0,z2,z3,z1106,z4,z5]),(0,[z0,z2,z3,z4,z543,z64]),(0,[z0,z2,z3,z4,z5,z1107])],[(0,[z0,z2,z3,z4,z5,z1108]),(0,[z35,z2,z3,z36,z50,z5]),(0,[z0,z2,z3,z9,z359,z5]),(0,[z0,z2,z3,z4,z5,z1109]),(0,[z0,z35,z2,z3,z5,z256])],[(0,[z0,z2,z3,z1110,z5,z6]),(0,[z123,z2,z3,z50,z5,z6]),(0,[z240,z2,z3,z50,z5,z6]),(0,[z0,z2,z3,z4,z1111,z6]),(0,[z0,z130,z16,z9,z4,z5]),(0,[z0,z2,z3,z9,z5,z414])],[(0,[z0,z2,z394,z4,z342,z6]),(0,[z0,z2,z3,z4,z5,z1112]),(0,[z0,z2,z3,z4,z1113,z6]),(0,[z0,z819,z2,z3,z155,z5]),(0,[z1114,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1115]),(0,[z0,z2,z3,z4,z484,z6]),(0,[z92,z2,z3,z4,z63,z127]),(0,[z0,z2,z3,z4,z5,z1116]),(0,[z0,z2,z3,z5,z199,z1044]),(0,[z0,z2,z3,z4,z5,z1117])],[(0,[z0,z2,z3,z1118,z5,z6]),(0,[z0,z2,z3,z4,z343,z316]),(0,[z92,z2,z3,z4,z13,z6]),(0,[z668,z0,z35,z2,z3,z5]),(0,[z681,z2,z3,z4,z5,z143]),(0,[z0,z2,z3,z1119,z4,z5]),(0,[z1120,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1121,z5,z6]),(0,[z0,z2,z1122,z4,z5,z6]),(0,[z0,z245,z47,z4,z5,z6]),(0,[z81,z245,z25,z4,z5,z6]),(0,[z0,z2,z3,z1123,z4,z5]),(0,[z1124,z2,z3,z4,z5,z6]),(0,[z88,z0,z2,z3,z5,z302]),(0,[z879,z106,z0,z2,z3,z5]),(0,[z1125,z2,z3,z4,z5,z6])],[(0,[z0,z126,z16,z4,z5,z6]),(0,[z88,z0,z2,z306,z4,z6]),(0,[z87,z2,z3,z4,z5,z143]),(0,[z0,z35,z2,z3,z30,z5]),(0,[z0,z2,z3,z4,z1126,z6]),(0,[z0,z2,z3,z86,z4,z5]),(0,[z0,z2,z47,z4,z235,z391]),(0,[z0,z2,z4,z715,z235,z6]),(0,[z0,z35,z2,z3,z59,z5]),(0,[z0,z719,z3,z9,z4,z5])]],
   [[(0,[z81,z2,z25,z4,z5,z98]),(0,[z2,z712,z25,z4,z5,z6]),(0,[z0,z2,z1127,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1128]),(0,[z0,z35,z2,z3,z4,z13]),(0,[z0,z2,z3,z4,z1129,z5])],[(0,[z77,z75,z3,z4,z5,z6]),(0,[z2,z3,z4,z887,z5,z6]),(0,[z0,z35,z2,z3,z50,z5]),(0,[z0,z35,z2,z213,z4,z5])],[(0,[z0,z35,z2,z78,z4,z5]),(0,[z14,z2,z3,z36,z13,z6]),(0,[z88,z0,z2,z3,z384,z6]),(0,[z0,z2,z3,z1130,z4,z5]),(0,[z0,z2,z3,z4,z5,z957]),(0,[z109,z0,z35,z3,z191,z5])],[(0,[z0,z2,z1131,z4,z5,z6]),(0,[z81,z2,z25,z4,z5,z6]),(0,[z0,z1132,z2,z3,z4,z5]),(0,[z0,z1133,z2,z3,z5,z6]),(0,[z0,z2,z1134,z4,z5,z6]),(0,[z0,z2,z3,z9,z4,z484]),(0,[z0,z2,z888,z4,z5,z6]),(0,[z0,z2,z3,z1135,z5,z6]),(0,[z0,z157,z2,z86,z17,z5]),(0,[z0,z2,z3,z4,z5,z1136]),(0,[z178,z0,z102,z3,z4,z5]),(0,[z441,z2,z3,z432,z4,z5]),(0,[z0,z2,z3,z9,z5,z782])],[(0,[z0,z2,z78,z4,z5,z588]),(0,[z0,z2,z1137,z3,z4,z5]),(0,[z0,z2,z3,z1138,z4,z5]),(0,[z0,z3,z4,z105,z801,z6])],[(0,[z362,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z1139,z5,z6])],[(0,[z0,z2,z3,z457,z5,z68]),(0,[z92,z2,z3,z189,z63,z6]),(0,[z0,z146,z3,z4,z107,z327]),(0,[z0,z2,z3,z4,z801,z6]),(0,[z0,z2,z3,z4,z5,z1140]),(0,[z0,z2,z3,z5,z385,z527])],[(0,[z0,z48,z29,z4,z5,z6]),(0,[z0,z35,z2,z3,z5,z468]),(0,[z0,z2,z4,z5,z6,z1141]),(0,[z0,z2,z3,z4,z5,z1142]),(0,[z109,z0,z280,z2,z3,z6]),(0,[z1143,z2,z3,z4,z5,z6]),(0,[z0,z2,z110,z133,z4,z5])]],
   [[(0,[z272,z35,z28,z3,z4,z5]),(0,[z0,z2,z3,z1006,z50,z5]),(0,[z0,z2,z3,z973,z5,z6]),(0,[z0,z2,z114,z4,z5,z1144]),(0,[z0,z2,z261,z3,z4,z338]),(0,[z0,z2,z4,z74,z715,z6]),(0,[z0,z2,z3,z4,z5,z509])],[(0,[z222,z35,z2,z3,z4,z45]),(0,[z0,z2,z306,z44,z4,z6]),(0,[z0,z2,z3,z1145,z5,z6]),(0,[z276,z0,z2,z520,z4,z5])],[(0,[z0,z2,z1146,z4,z5,z6]),(0,[z0,z2,z3,z1147,z4,z5]),(0,[z0,z510,z3,z53,z5,z6]),(0,[z0,z35,z2,z3,z5,z10]),(0,[z101,z0,z3,z4,z477,z5])],[(0,[z362,z2,z78,z4,z5,z6]),(0,[z120,z0,z3,z4,z400,z5]),(0,[z0,z2,z3,z4,z5,z1148]),(0,[z0,z1149,z3,z4,z5,z6]),(0,[z0,z2,z1150,z3,z4,z5]),(0,[z0,z2,z3,z4,z64,z736])],[(0,[z77,z75,z3,z181,z5,z6]),(0,[z14,z2,z3,z155,z5,z6]),(0,[z321,z2,z3,z4,z63,z6]),(0,[z0,z35,z117,z3,z4,z105]),(0,[z0,z2,z3,z4,z715,z6]),(0,[z0,z2,z3,z4,z5,z1033])],[(0,[z0,z1151,z3,z4,z5,z6]),(0,[z0,z2,z3,z1152,z4,z5])],[(0,[z0,z1153,z3,z4,z5,z6]),(0,[z0,z2,z1154,z3,z4,z5]),(0,[z0,z2,z3,z93,z388,z6]),(0,[z0,z2,z1155,z3,z4,z5]),(0,[z0,z2,z138,z763,z5,z6]),(0,[z0,z2,z3,z1156,z5,z6]),(0,[z88,z0,z35,z73,z2,z3]),(0,[z0,z2,z3,z4,z5,z1157])],[(0,[z0,z2,z3,z457,z112,z6]),(0,[z0,z2,z1158,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z533]),(0,[z0,z35,z2,z952,z4,z5])]],
   [[(0,[z0,z2,z1159,z3,z4,z6]),(0,[z454,z2,z3,z50,z5,z6]),(0,[z0,z2,z3,z866,z322,z6])],[(0,[z0,z2,z78,z9,z4,z5]),(0,[z0,z2,z1160,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1161]),(0,[z0,z2,z3,z4,z5,z1162]),(0,[z0,z3,z4,z5,z121,z877])],[(0,[z0,z2,z3,z4,z5,z588]),(0,[z0,z75,z78,z4,z5,z6]),(0,[z0,z2,z1163,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1164]),(1,[z0,z3,z4,z801,z6]),(0,[z0,z2,z247,z9,z4,z5]),(0,[z0,z35,z2,z3,z320,z5]),(0,[z0,z2,z138,z49,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1165]),(0,[z0,z2,z3,z1166,z4,z5]),(0,[z0,z117,z3,z4,z105,z6]),(0,[z1114,z35,z2,z3,z4,z5])],[(0,[z0,z35,z2,z3,z358,z5]),(0,[z362,z245,z3,z4,z5,z6]),(0,[z0,z2,z1167,z4,z5,z6]),(0,[z0,z2,z3,z155,z5,z127]),(0,[z401,z2,z3,z4,z5,z143]),(0,[z0,z35,z908,z3,z4,z5])],[(0,[z77,z75,z394,z4,z5,z6]),(0,[z362,z2,z4,z74,z5,z6]),(0,[z1120,z35,z2,z3,z4,z5])],[(0,[z0,z2,z3,z1168,z5,z6]),(0,[z0,z353,z29,z4,z5,z6]),(0,[z0,z2,z47,z234,z4,z6]),(0,[z0,z2,z3,z59,z5,z809])],[(0,[z0,z2,z3,z4,z5,z1169]),(0,[z0,z1097,z2,z3,z82,z5]),(0,[z0,z2,z3,z9,z104,z5]),(0,[z0,z2,z3,z1170,z5,z6]),(0,[z0,z2,z3,z1171,z4,z5]),(0,[z0,z2,z3,z4,z5,z877]),(0,[z0,z2,z3,z1172,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1173]),(0,[z0,z2,z3,z4,z5,z1174]),(0,[z0,z2,z3,z294,z4,z45]),(0,[z0,z2,z3,z4,z5,z1011])],[(0,[z362,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1175,z4,z5]),(0,[z0,z245,z3,z104,z5,z6]),(0,[z0,z2,z3,z4,z5,z1176]),(0,[z0,z2,z3,z1177,z4,z5]),(0,[z0,z640,z3,z4,z105,z6]),(0,[z0,z52,z3,z53,z5,z84]),(0,[z0,z117,z3,z4,z163,z6]),(0,[z1178,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z1179,z5,z6]),(0,[z0,z245,z3,z9,z4,z5]),(0,[z27,z2,z3,z4,z63,z6]),(0,[z106,z0,z35,z2,z3,z5]),(0,[z0,z2,z3,z4,z5,z1180]),(0,[z0,z2,z3,z9,z5,z385])],[(0,[z0,z2,z3,z1004,z4,z5]),(0,[z0,z2,z3,z4,z5,z1181]),(0,[z0,z2,z3,z93,z5,z330]),(0,[z0,z280,z2,z3,z442,z4]),(0,[z0,z2,z1182,z4,z5,z6]),(0,[z1183,z2,z3,z4,z5,z6]),(0,[z1184,z2,z3,z4,z5,z6]),(0,[z0,z1185,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1186])],[(0,[z0,z2,z3,z4,z1187,z6]),(0,[z0,z2,z3,z744,z189,z5]),(0,[z0,z597,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1188]),(0,[z0,z1189,z2,z3,z4,z5])],[(0,[z0,z2,z3,z181,z5,z588]),(0,[z92,z2,z3,z4,z63,z6]),(0,[z0,z2,z3,z4,z484,z143])],[(0,[z0,z2,z1190,z4,z5,z6]),(0,[z0,z2,z3,z1191,z4,z5]),(0,[z0,z2,z3,z104,z5,z6]),(0,[z81,z2,z25,z4,z343,z6]),(0,[z0,z2,z47,z4,z343,z6]),(0,[z0,z2,z3,z4,z1192,z5])],[(0,[z0,z2,z3,z82,z5,z316]),(0,[z0,z35,z2,z3,z4,z423]),(0,[z0,z2,z3,z1193,z5,z6]),(0,[z0,z2,z1194,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1195]),(0,[z0,z2,z3,z4,z5,z1196]),(0,[z1143,z35,z2,z3,z4,z5])]],
   [[(0,[z0,z2,z3,z1197,z104,z5]),(0,[z287,z2,z3,z4,z45,z6]),(0,[z222,z2,z3,z4,z45,z6]),(0,[z0,z1198,z2,z3,z4,z5]),(0,[z200,z0,z2,z4,z352,z5])],[(0,[z0,z2,z3,z1199,z4,z5]),(0,[z0,z146,z3,z199,z107,z6]),(0,[z0,z608,z3,z4,z5,z121]),(0,[z0,z35,z2,z3,z5,z527])],[(0,[z0,z2,z4,z561,z5,z6]),(0,[z0,z2,z138,z447,z5,z6]),(0,[z0,z52,z3,z53,z5,z6]),(0,[z0,z52,z3,z5,z251,z6]),(0,[z0,z2,z3,z44,z575,z6])],[(0,[z0,z2,z78,z4,z5,z68]),(0,[z0,z2,z3,z1200,z5,z6]),(0,[z0,z103,z3,z4,z5,z316]),(0,[z0,z1201,z2,z3,z5,z6]),(0,[z0,z2,z247,z4,z5,z829]),(1,[z0,z3,z4,z5,z877])],[(0,[z0,z2,z3,z4,z1202,z6]),(0,[z88,z0,z35,z146,z2,z3]),(0,[z148,z0,z244,z2,z3,z5])],[(0,[z0,z2,z3,z4,z5,z1203]),(0,[z88,z0,z35,z2,z3,z63])],[(0,[z0,z2,z3,z5,z1204,z6]),(0,[z0,z2,z3,z1205,z4,z5]),(0,[z0,z103,z3,z82,z5,z6]),(0,[z240,z0,z35,z2,z3,z5]),(0,[z0,z2,z1059,z4,z5,z6]),(0,[z434,z0,z2,z3,z4,z381]),(0,[z0,z2,z3,z1206,z5,z6])],[(0,[z0,z35,z2,z3,z657,z5]),(0,[z2,z3,z1207,z4,z5,z6]),(0,[z0,z2,z1208,z3,z4,z5]),(0,[z0,z35,z2,z247,z4,z5]),(0,[z0,z2,z3,z4,z5,z1209]),(0,[z0,z35,z2,z3,z5,z540])]],
   [[(0,[z0,z2,z3,z4,z5,z1210]),(0,[z0,z2,z3,z1197,z4,z5]),(0,[z27,z2,z3,z36,z5,z6]),(0,[z0,z117,z3,z9,z4,z105])],[(0,[z0,z2,z3,z4,z1211,z6]),(0,[z35,z160,z2,z3,z36,z5]),(0,[z1212,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1213])],[(0,[z0,z2,z3,z4,z112,z588]),(0,[z0,z2,z1214,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1215]),(0,[z0,z35,z2,z3,z36,z5]),(0,[z0,z280,z2,z3,z50,z6]),(0,[z0,z2,z3,z4,z5,z1216]),(0,[z109,z0,z3,z806,z5,z6]),(0,[z0,z2,z3,z1217,z4,z5]),(0,[z0,z2,z1218,z4,z5,z6])],[(0,[z0,z2,z3,z36,z13,z6]),(0,[z362,z2,z3,z4,z835,z6]),(1,[z0,z2,z4,z715,z6]),(0,[z0,z35,z2,z3,z655,z5]),(0,[z27,z2,z3,z9,z4,z5])],[(0,[z0,z2,z78,z4,z112,z6]),(0,[z0,z130,z360,z4,z5,z6]),(0,[z0,z2,z3,z9,z189,z5]),(0,[z0,z35,z2,z3,z89,z5])],[(0,[z0,z2,z3,z4,z5,z1219]),(0,[z0,z35,z2,z3,z637,z5]),(0,[z0,z2,z3,z4,z1220,z6])],[(0,[z0,z35,z2,z3,z4,z342]),(0,[z0,z2,z3,z4,z13,z15]),(0,[z0,z35,z2,z3,z432,z5]),(0,[z0,z35,z2,z3,z4,z815]),(0,[z0,z35,z2,z3,z679,z5])],[(0,[z0,z35,z2,z3,z1006,z5]),(0,[z0,z2,z3,z5,z6,z1221]),(0,[z0,z2,z3,z4,z5,z1144]),(0,[z0,z2,z138,z49,z5,z335]),(0,[z0,z1222,z2,z3,z4,z5]),(0,[z0,z2,z832,z9,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z5,z1223]),(0,[z0,z2,z3,z4,z1224,z6]),(0,[z65,z2,z3,z4,z484,z143]),(0,[z0,z2,z3,z1225,z4,z5]),(0,[z0,z3,z4,z5,z801,z6])],[(0,[z0,z2,z3,z4,z13,z6]),(0,[z287,z0,z35,z2,z3,z5]),(0,[z0,z2,z3,z93,z484,z6]),(0,[z362,z35,z2,z3,z4,z5]),(0,[z451,z654,z2,z3,z4,z5]),(0,[z0,z2,z3,z5,z164,z782])],[(0,[z0,z35,z2,z3,z633,z5]),(0,[z0,z2,z3,z4,z1226,z5]),(0,[z0,z2,z3,z4,z221,z64])],[(0,[z0,z2,z3,z5,z1227,z6]),(0,[z88,z0,z35,z2,z3,z221]),(0,[z0,z35,z808,z3,z4,z5]),(0,[z0,z2,z502,z395,z4,z5])],[(0,[z0,z35,z52,z3,z53,z5]),(0,[z0,z2,z4,z715,z5,z6]),(0,[z88,z0,z35,z2,z3,z5])],[(0,[z0,z2,z3,z9,z457,z5]),(0,[z0,z2,z3,z4,z5,z1228]),(0,[z0,z2,z47,z9,z4,z235])],[(0,[z0,z2,z3,z4,z5,z1229]),(0,[z362,z2,z25,z4,z5,z6]),(0,[z0,z1230,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z95]),(0,[z482,z2,z3,z4,z45,z6])],[(0,[z0,z35,z245,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1231])]],
   [[(0,[z0,z2,z306,z9,z4,z5]),(0,[z0,z35,z2,z3,z5,z416]),(0,[z106,z0,z2,z3,z5,z6]),(0,[z0,z244,z2,z3,z5,z184])],[(0,[z0,z2,z3,z4,z1232,z6]),(0,[z0,z2,z3,z104,z343,z6]),(0,[z238,z2,z3,z4,z5,z330]),(0,[z0,z280,z2,z3,z9,z4]),(0,[z88,z0,z2,z282,z3,z5])],[(0,[z0,z2,z3,z457,z5,z6]),(0,[z1233,z2,z3,z4,z5,z6]),(0,[z0,z146,z3,z9,z4,z107]),(0,[z0,z2,z3,z763,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1234]),(0,[z499,z2,z3,z4,z5,z330]),(0,[z0,z35,z230,z29,z4,z5]),(0,[z0,z2,z3,z1235,z4,z5]),(0,[z0,z2,z3,z4,z1236,z5]),(0,[z0,z2,z114,z9,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1237]),(0,[z0,z2,z3,z1238,z5,z6]),(0,[z0,z2,z3,z44,z373,z6]),(0,[z0,z2,z541,z3,z4,z5]),(0,[z0,z52,z3,z806,z5,z6]),(0,[z88,z0,z35,z2,z3,z322])],[(0,[z27,z2,z3,z4,z13,z6]),(0,[z120,z0,z3,z4,z5,z121]),(0,[z0,z35,z2,z3,z664,z5])],[(0,[z0,z1239,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z199,z1188]),(0,[z0,z2,z3,z4,z5,z809])],[(0,[z106,z0,z2,z3,z295,z5]),(0,[z757,z2,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1046).take 210) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1256)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 525, 210] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 108).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 202).take 54).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [108, 94, 54] = true :=
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

end PEqualNP.Outside.L_meta_38835

theorem PEqualNP.Outside.L_meta_38835 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4272611488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4272611488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38835.solve