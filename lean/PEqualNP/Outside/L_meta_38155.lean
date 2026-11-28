import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38155

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
  Nat.testBit (4294901486 * 2 ^ 32 + 4294506664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x5080208130891282#64 ++ 0x10a1004102611225#64 ++ 0xb540619330993ff5#64 ++ 0xf76a80c32661327f#64 : BitVec 256),
   (0x85008224c3162944#64 ++ 0x810a010449862c52#64 ++ 0x6ce1866cc31e39f3#64 ++ 0xeed9c30cd9863c73#64 : BitVec 256),
   (0x0602087001224c10#64 ++ 0x220c0410e0024498#64 ++ 0xe3c6187003e7ce6f#64 ++ 0x5dc78c30e007cf9c#64 : BitVec 256),
   (0x180817805405b000#64 ++ 0xc030102f00a80b60#64 ++ 0x1fd81f80fc07f05f#64 ++ 0x3c3fb03f01f80fe0#64 : BitVec 256),
   (0xe015e000aad80007#64 ++ 0x05c02bc00155b000#64 ++ 0xffdfe000fff8003f#64 ++ 0x03ffbfc001fff000#64 : BitVec 256),
   (0x001f5d5a00000018#64 ++ 0x06003ebab4000000#64 ++ 0xffffffff00000000#64 ++ 0xfffffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00000000 0xfffffffffe000000

def z1 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x428618600366c00a 0x08850c30c006cd80

def z2 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003e7ce6f 0x5dc78c30e007cf9c

def z3 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc07f05f 0x3c3fb03f01f80fe0

def z4 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330993ff5 0xf76a80c32661327f

def z5 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31e39f3 0xeed9c30cd9863c73

def z6 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff8003f 0x03ffbfc001fff000

def z7 : W := mkw 0x4080200120880282 0x1081004002411005 0xa000601300980fa0 0xc34000c02601301f

def z8 : W := mkw 0x568228f131ab5e92 0x32ad0451e26356bd 0xf7c679f333ffffff 0xffef8cf3e667ffff

def z9 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x9f1fe000fcf8001c 0x033e3fc001f9f000

def z10 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x1c39e78f00000000 0xa23873cf1e000000

def z11 : W := mkw 0xe01ffd5aaad8001f 0x07c03ffab555b000 0xfffffffffff8003f 0xfffffffffffff000

def z12 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x931e799300000000 0x11263cf326000000

def z13 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x00000000c31e39f3 0x0000000001863c73

def z14 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0x00201fff00000000 0xfc00403ffe000000

def z15 : W := mkw 0x0015400000000000 0x04002a8000000000 0xffdfe00000000000 0x03ffbfc000000000

def z16 : W := mkw 0xe600a020abfa4c07 0x21cc01404157f498 0x00000000ffffce7f 0x0000000001ffff9c

def z17 : W := mkw 0x87028a74c3366d54 0xa30e0514e9866cda 0xebe79e7cc3e7ce6f 0x5dd7cf3cf987cf9c

def z18 : W := mkw 0x0200000000204400 0x2004000000004088 0x0000000000e1c60c 0x000000000001c38c

def z19 : W := mkw 0x87028a74c3366d54 0xa30e0514e9866cda 0xefe79e7cc3ffffff 0xffdfcf3cf987ffff

def z20 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x00001f80fc07f05f 0x3c00003f01f80fe0

def z21 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0x00000000fff8003f 0x0000000001fff000

def z22 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6fe19e6cc31ff9ff 0xfedfc33cd9863ff3

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0xa140001000810e65 0x554280002001021c

def z24 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xede1867cc39f3ff7 0xffdbc30cf9873e7f

def z25 : W := mkw 0x781d77807ccdb003 0xc4f03aef00f99b60 0x9fde7f80fce7f05f 0x3d3fbcff01f9cfe0

def z26 : W := mkw 0x0008150000000000 0x0000102a00000000 0x1318198000000000 0x1026303300000000

def z27 : W := mkw 0x0015400000000000 0x04002a8000000000 0xffdfe000fc00001f 0x03ffbfc001f80000

def z28 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe006007003e00e20 0x41c00c00e007c01c

def z29 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xe007e00003f80020 0x03c00fc00007f000

def z30 : W := mkw 0x0400002001020800 0x0008000040020410 0x63c018600307c86f 0x5cc78030c0060f90

def z31 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0x1fd81f93fc07ffdf 0xfc3fb03f27f80fff

def z32 : W := mkw 0x811dd70ec214214c 0x85023bae1d842842 0x1c39e78fc0183190 0xa23873cf1f803063

def z33 : W := mkw 0x1808158014019000 0x4030102b00280320 0x131819803c01c00c 0x1026303300780380

def z34 : W := mkw 0x58883781748db282 0xd0b1106f02e91b65 0xbfd87f93fc9fffff 0xff7fb0ff27f93fff

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3c6000000000000 0x01c78c0000000000

def z36 : W := mkw 0x181f5fda5405b018 0xc6303ebfb4a80b60 0xfffffffffc07f05f 0xfffffffffff80fe0

def z37 : W := mkw 0x080817004404a000 0xc010102e00880940 0x00001e000006c000 0x0800003c00000d80

def z38 : W := mkw 0x4000200020880002 0x0080004000411000 0xb540600030980035 0x036a80c000613000

def z39 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x4a9f8000cf60000a 0x00953f00019ec000

def z40 : W := mkw 0x601f7d5a28c8001b 0x06c03efab4519000 0xffffffff3ce0000c 0xfffffffffe79c000

def z41 : W := mkw 0x1e0a1ff05527fc10 0xe23c143fe0aa4ff8 0xffde1ff0ffe7fe7f 0x7dffbc3fe1ffcffc

def z42 : W := mkw 0x0500022441062940 0x800a000448820c52 0x0020066c000639c0 0xec00400cd8000c73

def z43 : W := mkw 0x81008204c2142144 0x8102010409842842 0x0c21860cc0183190 0xa218430c19803063

def z44 : W := mkw 0x0808150004008000 0x4010102a00080100 0x021818000c00c008 0x0004303000180180

def z45 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x48a1866cc30639c2 0xec91430cd9860c73

def z46 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0xe3c60000fff8003f 0x01c78c0001fff000

def z47 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x000000000007f040 0x0000000000000fe0

def z48 : W := mkw 0x87028a74c3366d54 0xa30e0514e9866cda 0xece7867cc3fe3ff3 0xefd9cf0cf987fc7f

def z49 : W := mkw 0x1000008010011000 0x0020000100200220 0x1540018030013055 0x342a800300600260

def z50 : W := mkw 0x081f5f5a4404a018 0xc6103ebeb4880940 0xffffffffcc06c00a 0xffffffffff980d80

def z51 : W := mkw 0x509f7ddb3089129a 0x16a13efbb6611225 0x931e799330810604 0x11263cf32661020c

def z52 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfc3fe7ff00000000 0xe3f87fcffe000000

def z53 : W := mkw 0x1e0a1ff05527fc10 0xe23c143fe0aa4ff8 0x00001ff00007fe40 0x7c00003fe0000ffc

def z54 : W := mkw 0x0008150000000000 0x0000102a00000000 0x1fd81f8000000000 0x3c3fb03f00000000

def z55 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xf33ff9ff00000000 0xd3e67ff3fe000000

def z56 : W := mkw 0x9d0082a4d717b944 0xc13a010549ae2f72 0x00000000ff1ff9ff 0x0000000001fe3ff3

def z57 : W := mkw 0x781d75803cc99003 0x44f03aeb00799320 0x931e79803ce1c00c 0x11263cf30079c380

def z58 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0a981f80cc07f04a 0x3c15303f01980fe0

def z59 : W := mkw 0x0008150000000000 0x0000102a00000000 0x0a981e0000000000 0x0815303c00000000

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x6ce1866c00000000 0xeed9c30cd8000000

def z61 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x13181980fc07f05f 0x1026303301f80fe0

def z62 : W := mkw 0x4000200020880002 0x0080004000411000 0x9100600030800004 0x012200c000610000

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0xb540619300000000 0xf76a80c326000000

def z64 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe193fff8003f 0xf7ffbfc327fff000

def z65 : W := mkw 0x509f7ddb3089129a 0x16a13efbb6611225 0xffffffff30993ff5 0xfffffffffe61327f

def z66 : W := mkw 0x9d0897a4d717b944 0xc13a112f49ae2f72 0x7ff99fecff1ff9ff 0xfefff33fd9fe3ff3

def z67 : W := mkw 0xe515e224ebde2947 0x85ca2bc449d7bc52 0xffffe66cfffe39ff 0xefffffccd9fffc73

def z68 : W := mkw 0x0015400000000000 0x04002a8000000000 0xffdfe19300000000 0xf7ffbfc326000000

def z69 : W := mkw 0x1080008110011280 0x1021000102200225 0x0000019300013fc0 0xf40000032600027f

def z70 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0xe027e07f00000000 0xc3c04fc0fe000000

def z71 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x00000000fc07f05f 0x0000000001f80fe0

def z72 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x5e9fe000ff78001a 0x02bd3fc001fef000

def z73 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xebff9e7c00000000 0x5dd7ff3cf8000000

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0x8306000000e0000c 0x01060c000001c000

def z75 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3c6000003e0002f 0x01c78c000007c000

def z76 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff03e0002f 0xfffffffffe07c000

def z77 : W := mkw 0xf095e081bad91287 0x15e12bc10375b225 0xf547e19333f93ff5 0xf7ea8fc32667f27f

def z78 : W := mkw 0xd580a2a5f39f3bc6 0x91ab01454be73e77 0xfde1e7fff39f3ff7 0xfffbc3cfffe73e7f

def z79 : W := mkw 0x050a1f7e41062958 0x820a143efc820c52 0x00201fff000639c0 0xfc00403ffe000c73

def z80 : W := mkw 0xe617e870abfa4c17 0x27cc2fd0e157f498 0xffdff870ffffce7f 0x5fffbff0e1ffff9c

def z81 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe7c6187003ffffff 0xffcf8c30e007ffff

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x24400000001839f1 0xe648800000003073

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020066c00000000 0xec00400cd8000000

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0xb5406193001839f1 0xf76a80c326003073

def z85 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff001839f1 0xfffffffffe003073

def z86 : W := mkw 0x5095608130891282 0x14a12ac102611225 0xffdfe19330993ff5 0xf7ffbfc32661327f

def z87 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x4006006003600000 0x00800c00c006c000

def z88 : W := mkw 0x0400002001020800 0x0008000040020410 0x4080006003060002 0x08810000c0060c00

def z89 : W := mkw 0x87028a74c3366d54 0xa30e0514e9866cda 0x4aa79e6cc366c00a 0x08954f3cd986cd80

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000007c04f 0x0000000000000f80

def z91 : W := mkw 0xe615e020abfa4c07 0x25cc2bc04157f498 0xffdfe000ffffce7f 0x03ffbfc001ffff9c

def z92 : W := mkw 0x4682287121aa4e92 0x328d0450e243549d 0xe006607303f80fa0 0xc3c00cc0e607f01f

def z93 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xeabffe7f00000000 0xcbd57ffcfe000000

def z94 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x48a1866cc3060002 0x0891430cd9860c00

def z95 : W := mkw 0x9d0082a4d717b944 0xc13a010549ae2f72 0x6ce1866cff1ff9ff 0xeed9c30cd9fe3ff3

def z96 : W := mkw 0x0600002001224c00 0x200c000040024498 0xe3c6000003e7ce6f 0x01c78c000007cf9c

def z97 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb400619330983fb0 0xe36800c32661307f

def z98 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xf547e00033f80035 0x03ea8fc00067f000

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fd80000fc00001f 0x003fb00001f80000

def z100 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6021866c031e39e0 0xeec0430cd8063c73

def z101 : W := mkw 0x080817004404a000 0xc010102e00880940 0x0ed81e00cc06f05b 0x2c1db03c01980de0

def z102 : W := mkw 0x0202085000204410 0x22040410a0004088 0xa346181000e1ce6d 0x55468c302001c39c

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x48a1866c00000000 0x0891430cd8000000

def z104 : W := mkw 0x871fdf7ec3366d5c 0xa70e3fbefd866cda 0xffffffffc3ffffff 0xffffffffff87ffff

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0000000060043 0x0c01800000000c00

def z106 : W := mkw 0x0400002001020800 0x0008000040020410 0x60c0006003060863 0x4cc18000c0060c10

def z107 : W := mkw 0x5080208130891282 0x10a1004102611225 0x0000000030993ff5 0x000000000061327f

def z108 : W := mkw 0x5080208130891282 0x10a1004102611225 0xfde1e7ff30993ff5 0xfffbc3cffe61327f

def z109 : W := mkw 0x0000000000000000 0x0000000000000000 0x60c0006000000000 0x4cc18000c0000000

def z110 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe00003f80020 0x03ffbfc00007f000

def z111 : W := mkw 0x181f5fda5405b018 0xc6303ebfb4a80b60 0x9fde7f93fc07f05f 0x3d3fbcff27f80fe0

def z112 : W := mkw 0x5080208130891282 0x10a1004102611225 0x34406183301839f1 0xe66880c306603073

def z113 : W := mkw 0x8d089724c716a944 0xc11a112e498e2d52 0x4ab99e6ccf06c00a 0x0895733cd99e0d80

def z114 : W := mkw 0xa81dd700ce54a005 0xc5503bae019ca940 0x4a9f9e00cf66c00a 0x08953f3c019ecd80

def z115 : W := mkw 0x060a1d7a01224c18 0x220c143af4024498 0x00201fff0007ce40 0xfc00403ffe000f9c

def z116 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x931e6000fff8003f 0x01263cc001fff000

def z117 : W := mkw 0x851fdf7ec316295c 0x870a3fbefd862c52 0xffffffffc31e39f3 0xffffffffff863c73

def z118 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x1ff9ff8f00000000 0xbe3ff3ff1e000000

def z119 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe306187003e1ce2c 0x51c60c30e007c39c

def z120 : W := mkw 0x5080208130891282 0x10a1004102611225 0xa000619300993fe0 0xf74000c32601327f

def z121 : W := mkw 0x061f5d7a01224c18 0x260c3ebaf4024498 0xffffffff03e7ce6f 0xfffffffffe07cf9c

def z122 : W := mkw 0x81008204c2142144 0x8102010409842842 0x6ce1866cc0183190 0xeed9c30cd9803063

def z123 : W := mkw 0x0600002001224c00 0x200c000040024498 0x0000000003e7ce6f 0x000000000007cf9c

def z124 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0x6cc18000fff8003f 0x02d9830001fff000

def z125 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1c180780fc003010 0x2038300f01f80060

def z126 : W := mkw 0xe415e020abda0807 0x05c82bc04157b410 0xffdfe060fffe087f 0x4fffbfc0c1fffc10

def z127 : W := mkw 0x0000020040042000 0x8000000400800840 0x0fc01e00c007f05f 0x3c1f803c01800fe0

def z128 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x428618700367ce4a 0x5c850c30e006cf9c

def z129 : W := mkw 0x8500802483120944 0x010a010049062412 0x6021806c031809a0 0xc2c04300d8063013

def z130 : W := mkw 0x851fdf7ec316295c 0x870a3fbefd862c52 0xffffffffc3060002 0xffffffffff860c00

def z131 : W := mkw 0x168208f111235e90 0x322d0411e22246bd 0xe3c619f303e7ffef 0xfdc78c33e607cfff

def z132 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0c21866cc01e39d0 0xee18430cd9803c73

def z133 : W := mkw 0xf800a280feddb007 0xc1f0014501fdbb60 0x00000000fffff07f 0x0000000001ffffe0

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x6ce1866c001839f1 0xeed9c30cd8003073

def z135 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe010fff90e7f 0x57ffbfc021fff21c

def z136 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xbd59e000fc980035 0x037ab3c001f93000

def z137 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xfc1fe000fff80030 0x03f83fc001fff000

def z138 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x1c19e000fc180010 0x023833c001f83000

def z139 : W := mkw 0x4080200120880282 0x1081004002411005 0xa440601300983ff1 0xe74880c02601307f

def z140 : W := mkw 0xf81df780feddb007 0xc5f03bef01fdbb60 0x1c19e780fc183010 0x223833cf01f83060

def z141 : W := mkw 0x801fdd5a8210001c 0x07003fbab5042000 0xffffffffc3180033 0xffffffffff863000

def z142 : W := mkw 0xa515c224cb562945 0x854a2b844996ac52 0x4abf866ccf66000a 0x08957f0cd99ecc00

def z143 : W := mkw 0xd580a2a5f39f3bc6 0x91ab01454be73e77 0xb5406193f39f3ff7 0xf76a80c327e73e7f

def z144 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xf31fe0003ff8002c 0x03e63fc0007ff000

def z145 : W := mkw 0x568228f131ab5e92 0x32ad0451e26356bd 0xe3c6187033ffffff 0x5dc78c30e067ffff

def z146 : W := mkw 0xe01df50aaad8000f 0x05c03bea1555b000 0x1c39e78ffc180010 0xa23873cf1ff83000

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0xb540619300810e65 0xf76a80c32601021c

def z148 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0x0000000003f80020 0x000000000007f000

def z149 : W := mkw 0x0008170040042000 0x8000102e00800840 0x1fd81f80c0063053 0x3c3fb03f01800c60

def z150 : W := mkw 0x8100800482100144 0x0102010009042002 0x0021800c00180180 0x8200430018003003

def z151 : W := mkw 0x0202085000204410 0x22040410a0004088 0x8006001000e00600 0x01000c002001c00c

def z152 : W := mkw 0x1e0817a05527fc00 0xe03c102f40aa4ff8 0x1fd81f80ffe7fe7f 0x3c3fb03f01ffcffc

def z153 : W := mkw 0x0402087001020810 0x02080410e0020410 0xe3c6187003060863 0x5dc78c30e0060c10

def z154 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1b981f80fc07c00e 0x1837303f01f80f80

def z155 : W := mkw 0x851dd72ec316294c 0x850a3bae5d862c52 0x7cf9e7efc31e39f3 0xeef9f3cfdf863c73

def z156 : W := mkw 0x0600002001224c00 0x200c000040024498 0xa140001003e7ce6f 0x554280002007cf9c

def z157 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x0000007000000e00 0x40000000e000001c

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c018000007c04f 0x1c07803000000f80

def z159 : W := mkw 0x0000000000000000 0x0000000000000000 0xffde0000ffe0003f 0x01ffbc0001ffc000

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c21860c00000000 0xa218430c18000000

def z161 : W := mkw 0x0002085000000010 0x02000410a0000000 0xf7c679f300000000 0xffef8cf3e6000000

def z162 : W := mkw 0xf89df781feddb287 0xd5f13bef03fdbb65 0xffdfff93ffffffff 0xffffbfff27ffffff

def z163 : W := mkw 0x568228f131ab5e92 0x32ad0451e26356bd 0xf3c679f333e7ce6f 0x5de78cf3e667cf9c

def z164 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x15401f803007f055 0x3c2a803f00600fe0

def z165 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0x931e60003ce0000c 0x01263cc00079c000

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000003e0002f 0x000000000007c000

def z167 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x48a1866cc31e39f3 0x0891430cd9863c73

def z168 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x5ebfffef00000000 0xaabd7fffde000000

def z169 : W := mkw 0x061f5d7a01224c18 0x260c3ebaf4024498 0xffffffff0007ce40 0xfffffffffe000f9c

def z170 : W := mkw 0x080817004404a000 0xc010102e00880940 0x1fd81e00fc06c01f 0x083fb03c01f80d80

def z171 : W := mkw 0x0008150000000000 0x0000102a00000000 0x1c18078000000000 0x2038300f00000000

def z172 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe006007003e7ce6f 0x41c00c00e007cf9c

def z173 : W := mkw 0x5080208130891282 0x10a1004102611225 0xbfd86193fc993fff 0xf77fb0c327f9327f

def z174 : W := mkw 0x8000800082100004 0x0100010001042000 0x6cc18000c3180033 0x02d9830001863000

def z175 : W := mkw 0x181d578a5405b008 0xc4303aaf14a80b60 0x1c39e78ffc003010 0xa23873cf1ff80060

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x2440000000000000 0xe648800000000000

def z177 : W := mkw 0x5080208130891282 0x10a1004102611225 0xf7c6619333f93fff 0xf7ef8cc32667f27f

def z178 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x1fd80000fc07f05f 0x003fb00001f80fe0

def z179 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x7cd9e000ff180033 0x02f9b3c001fe3000

def z180 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9100619330993ff5 0x112200c32661327f

def z181 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0x0000199300000000 0x1000003326000000

def z182 : W := mkw 0x528228d130a95692 0x32a50451a26152ad 0xb746799330f9fffd 0xf76e8cf32661f3ff

def z183 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xecc7e000c3f80033 0x03d98fc00187f000

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0xfde1e7ff00000000 0xfffbc3cffe000000

def z185 : W := mkw 0x07020a7441266d50 0xa20e0414e8824cda 0xe3e61e7c03e7ffef 0xfdc7cc3cf807cfff

def z186 : W := mkw 0x1800008014019000 0x4030000100280320 0x000000003c01c00c 0x0000000000780380

def z187 : W := mkw 0xf815e280feddb007 0xc5f02bc501fdbb60 0xffdfe000fffff07f 0x03ffbfc001ffffe0

def z188 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd81f90fc87fe7f 0x7d7fb03f21f90ffc

def z189 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9500619330993794 0xb32a00c32661326f

def z190 : W := mkw 0x181f5dda14019018 0x46303ebbb4280320 0x931e79933c01c00c 0x11263cf326780380

def z191 : W := mkw 0x0202085000204410 0x22040410a0004088 0xe3c6187000e1c60c 0x5dc78c30e001c38c

def z192 : W := mkw 0x958082a5d3173bc4 0x912b01054ba62e77 0x6ce187ffc31f3ff3 0xfed9c30fff863e7f

def z193 : W := mkw 0x4097685b2088029a 0x16812ed0b6411005 0xe027e07f00980fa0 0xc3c04fc0fe01301f

def z194 : W := mkw 0x5e8a3ff175affe92 0xf2bd147fe2eb5ffd 0xffde7ff3ffffffff 0xffffbcffe7ffffff

def z195 : W := mkw 0x061f5d7a01224c18 0x260c3ebaf4024498 0xffffffff03e00e20 0xfffffffffe07c01c

def z196 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f800007f040 0x3c3fb03f00000fe0

def z197 : W := mkw 0x0202085000204410 0x22040410a0004088 0x8306181000e1c60c 0x11060c302001c38c

def z198 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x7cf9e7ef00000000 0xeef9f3cfde000000

def z199 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xffdfe013fff80fbf 0xc3ffbfc027fff01f

def z200 : W := mkw 0x1e0a1df01523dc10 0x623c143be02a47b8 0xf3de19f03fe7ce6f 0x5de7bc33e07fcf9c

def z201 : W := mkw 0x0008150000000000 0x0000102a00000000 0x1fd81f80fc00001f 0x3c3fb03f01f80000

def z202 : W := mkw 0xf095e081bad91287 0x15e12bc10375b225 0xffdfe193fff93fff 0xf7ffbfc327fff27f

def z203 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xf7c679f303e7ce6f 0xffef8cf3e607cf9c

def z204 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6c21866cc31839b0 0xe2d8430cd9863073

def z205 : W := mkw 0x5080208130891282 0x10a1004102611225 0x15406183301931d5 0xb62a80c306603263

def z206 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0x6ce1866cc3ffffff 0xeed9c30cd987ffff

def z207 : W := mkw 0x0500022441062940 0x800a000448820c52 0x00000000000639c0 0x0000000000000c73

def z208 : W := mkw 0x080817004404a000 0xc010102e00880940 0x0a981e00cc06c00a 0x0815303c01980d80

def z209 : W := mkw 0x8d089724c716a944 0xc11a112e498e2d52 0x6ef99e6ccf1ef9fb 0xeeddf33cd99e3df3

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000039c0 0xe400000000000073

def z211 : W := mkw 0xe500a224ebde2947 0x81ca014449d7bc52 0x6ce1866cfffe39ff 0xeed9c30cd9fffc73

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0xe006000003e00020 0x01c00c000007c000

def z213 : W := mkw 0x811fdf5ec214215c 0x87023fbebd842842 0xffffffffc0183190 0xffffffffff803063

def z214 : W := mkw 0x080002004404a000 0xc010000400880940 0x00000000cc06c00a 0x0000000001980d80

def z215 : W := mkw 0x07020a7441266d50 0xa20e0414e8824cda 0x00201e7c0007ffc0 0xfc00403cf8000fff

def z216 : W := mkw 0xf015e080bad91007 0x05e02bc10175b220 0xffdfe180fff9307f 0x37ffbfc301fff260

def z217 : W := mkw 0xe515e224ebde2947 0x85ca2bc449d7bc52 0xece7e66cc3fe39f3 0xefd9cfccd987fc73

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x9100619300000000 0x112200c326000000

def z219 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x0001e00000180000 0x020003c000003000

def z220 : W := mkw 0x080817004404a000 0xc010102e00880940 0x08180600cc000000 0x0010300c01980000

def z221 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1400619330193fd0 0xf62800c32660327f

def z222 : W := mkw 0x58883781748db282 0xd0b1106f02e91b65 0xbd586793fc993ff5 0xf77ab0cf27f9327f

def z223 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x5fdf8000ff60001f 0x00bfbf0001fec000

def z224 : W := mkw 0x0015400a00000008 0x04002a8014000000 0x0021e00f00000000 0x820043c01e000000

def z225 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x60c00060c31e39f3 0x4cc18000c1863c73

def z226 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x000018700007ce40 0x5c000030e0000f9c

def z227 : W := mkw 0x0600002001224c00 0x200c000040024498 0x0000000003e00e20 0x000000000007c01c

def z228 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x0cc00600fc07f05f 0x2c19800c01f80fe0

def z229 : W := mkw 0xd180a285f29d33c6 0x91a301450be53a67 0xbd61e79ff0993ff5 0xf77ac3cf3fe1327f

def z230 : W := mkw 0xa515c224cb562945 0x854a2b844996ac52 0x6eff866ccf7e39fb 0xeeddff0cd99efc73

def z231 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x1018618300000000 0x002030c306000000

def z232 : W := mkw 0xe01ffd5aaad8001f 0x07c03ffab555b000 0xfffffe6cfff8003f 0x0bfffffcd9fff000

def z233 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0xe3e61fff00000000 0xfdc7cc3ffe000000

def z234 : W := mkw 0x509768db3089129a 0x16a12ed1b6611225 0xf567e1ff30993ff5 0xf7eacfc3fe61327f

def z235 : W := mkw 0xd580a2a5f39f3bc6 0x91ab01454be73e77 0x6ce1866cf39f3ff7 0xeed9c30cd9e73e7f

def z236 : W := mkw 0x0008150000000000 0x0000102a00000000 0x7ff99fec00000000 0xfefff33fd8000000

def z237 : W := mkw 0x1000008010011000 0x0020000100200220 0xb540619330013055 0xf76a80c326600260

def z238 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x4a9f8000fff8003f 0x00953f0001fff000

def z239 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff0007c04f 0xfffffffffe000f80

def z240 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x00001f800007f040 0x3c00003f00000fe0

def z241 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe006187003e7ce60 0x5dc00c30e007cf9c

def z242 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xc386187003e7c60e 0x19870c30e007cf8c

def z243 : W := mkw 0xe515e224ebde2947 0x85ca2bc449d7bc52 0xffffe66cfffe003f 0x0bffffccd9fffc00

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x8100001000810604 0x110200002001020c

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x428600000360000a 0x00850c000006c000

def z246 : W := mkw 0x1d0817a45507b940 0xc03a102f48aa0f72 0x00201fec0007f9c0 0xfc00403fd8000ff3

def z247 : W := mkw 0x58802281748db282 0xd0b1004502e91b65 0xb5406193fc9fffff 0xf76a80c327f93fff

def z248 : W := mkw 0xfd1df7a4ffdfb947 0xc5fa3bef49ffbf72 0xffffffecfffff9ff 0xffffffffd9fffff3

def z249 : W := mkw 0x0500002401020940 0x000a000048020412 0x0020006c00000980 0xc0004000d8000013

def z250 : W := mkw 0xe617e870abfa4c17 0x27cc2fd0e157f498 0xffdff860fffec03f 0x0bffbff0c1fffd80

def z251 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xa14018700087ce65 0x5d428030e0010f9c

def z252 : W := mkw 0x0000020040042000 0x8000000400800840 0x00000000c0063053 0x0000000001800c60

def z253 : W := mkw 0x4080200120880282 0x1081004002411005 0x0000600300180180 0x820000c006003003

def z254 : W := mkw 0xe015e200eadc2007 0x85c02bc401d5b840 0xffdfe600fffe307f 0x2fffbfcc01fffc60

def z255 : W := mkw 0xf080a081bad91287 0x11e101410375b225 0x00000000fff93fff 0x0000000001fff27f

def z256 : W := mkw 0x6000200028c80003 0x00c0004000519000 0x000000003ce0000c 0x000000000079c000

def z257 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1e981f80fc06f01a 0x283d303f01f80de0

def z258 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x4abf9e6c00000000 0x08957f3cd8000000

def z259 : W := mkw 0xd59ffffff39f3bde 0x97ab3fffffe73e77 0xfffffffff39f3ff7 0xffffffffffe73e7f

def z260 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb7c07993309fffff 0xff6f80f326613fff

def z261 : W := mkw 0x1000008010011000 0x0020000100200220 0x0000000030013055 0x0000000000600260

def z262 : W := mkw 0xf81df780feddb007 0xc5f03bef01fdbb60 0xffdfff80fffff07f 0x3fffbfff01ffffe0

def z263 : W := mkw 0x180a1fd05405b010 0xc230143fa0a80b60 0xffde1ff0fc07f05f 0x7dffbc3fe1f80fe0

def z264 : W := mkw 0x4000200020880002 0x0080004000411000 0x1400600030180010 0x022800c000603000

def z265 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0x00000000c3ffffff 0x000000000187ffff

def z266 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffffe66cfff8003f 0xefffffccd9fff000

def z267 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1400618330183190 0xa22800c306603063

def z268 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x68a1866cc31e09a2 0xcad1430cd9863c13

def z269 : W := mkw 0xe017e850aad80017 0x07c02fd0a155b000 0xffdff870fff8003f 0x5fffbff0e1fff000

def z270 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fc180010 0x03ffbfc001f83000

def z271 : W := mkw 0x85089724c3162944 0x810a112e49862c52 0x7ff99fecc31e39f3 0xfefff33fd9863c73

def z272 : W := mkw 0xd180a285f29d33c6 0x91a301450be53a67 0x1c21e78ff0183190 0xa23843cf1fe03063

def z273 : W := mkw 0x061f5d7a01224c18 0x260c3ebaf4024498 0x4abf9e6c0366c00a 0x08957f3cd806cd80

def z274 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9100619330810604 0x112200c32661020c

def z275 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6007003e00e2f 0x41c78c00e007c01c

def z276 : W := mkw 0x508228d130891292 0x12a10451a2611225 0xf7c679f330993ff5 0xffef8cf3e661327f

def z277 : W := mkw 0xfe1ffff0fffffc17 0xe7fc3fffe1fffff8 0xffdffff0fffffe7f 0x7fffbfffe1fffffc

def z278 : W := mkw 0x0000000000000000 0x0000000000000000 0x2040000000000861 0x4440800000000010

def z279 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0a981e00fc07f05f 0x0815303c01f80fe0

def z280 : W := mkw 0xe01ffd5aaad8001f 0x07c03ffab555b000 0xffdff993fff8003f 0x13ffbff327fff000

def z281 : W := mkw 0x81008204c2142144 0x8102010409842842 0x0821860cc0000000 0x0010430c19800000

def z282 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330990635 0x136a80c32661320c

def z283 : W := mkw 0xe61ffd7aabfa4c1f 0x27cc3ffaf557f498 0xffffffffffffce7f 0xffffffffffffff9c

def z284 : W := mkw 0x5080208130891282 0x10a1004102611225 0xa140001030993ff5 0x554280002061327f

def z285 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfffffe6c00000000 0x0bfffffcd8000000

def z286 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xfde1e7ffc31e39f3 0xfffbc3cfff863c73

def z287 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6cc18000c31e39f3 0x02d9830001863c73

def z288 : W := mkw 0x0002085000000010 0x02000410a0000000 0xe3c6187000810e65 0x5dc78c30e001021c

def z289 : W := mkw 0x181f5fda5405b018 0xc6303ebfb4a80b60 0xfffffffffc003010 0xfffffffffff80060

def z290 : W := mkw 0x080817004404a000 0xc010102e00880940 0x0bd81e00cc07c04f 0x1c17b03c01980f80

def z291 : W := mkw 0x0008150000000000 0x0000102a00000000 0x00001f8000000000 0x3c00003f00000000

def z292 : W := mkw 0x0000020040042000 0x8000000400800840 0x0c000600c0003010 0x2018000c01800060

def z293 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1c181f80fc07f050 0x3c38303f01f80fe0

def z294 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb5406183309831b5 0xa36a80c306613063

def z295 : W := mkw 0x589f7fdb748db29a 0xd6b13effb6e91b65 0xfffffffffc9fffff 0xfffffffffff93fff

def z296 : W := mkw 0x80008200c2142004 0x8100010401842840 0x6cc18600c31e3073 0x2ed9830c01863c60

def z297 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0x00000000fc180010 0x0000000001f83000

def z298 : W := mkw 0x5080208130891282 0x10a1004102611225 0xa000601330993ff5 0xc34000c02661327f

def z299 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x4007800003600000 0x00800f000006c000

def z300 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x00000000fc003010 0x0000000001f80060

def z301 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x4ca1866cc31e3192 0xaa99430cd9863c63

def z302 : W := mkw 0xe617e870abfa4c17 0x27cc2fd0e157f498 0xe007e07003f80e20 0x43c00fc0e007f01c

def z303 : W := mkw 0xe01ffd5aaad8001f 0x07c03ffab555b000 0xffffffff03f80020 0xfffffffffe07f000

def z304 : W := mkw 0x0400002001020800 0x0008000040020410 0x6ce1866c03060863 0xeed9c30cd8060c10

def z305 : W := mkw 0x99089784d615b144 0xc132112f09ac2b62 0x1c39878cfc183190 0xa238730f19f83063

def z306 : W := mkw 0x108a1ddb10011298 0x1221143bb6200225 0x00201fff00013fc0 0xfc00403ffe00027f

def z307 : W := mkw 0x1808158014019000 0x4030102b00280320 0x1fd81f803c01c00c 0x3c3fb03f00780380

def z308 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0xffdfe0003ce0000c 0x03ffbfc00079c000

def z309 : W := mkw 0x0400002001020800 0x0008000040020410 0x6000006003000820 0x40c00000c0060010

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000001000010e40 0x540000002000021c

def z311 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0x9fde6000fce0001f 0x013fbcc001f9c000

def z312 : W := mkw 0x0600002001224c00 0x200c000040024498 0x60c0006003e7ce6f 0x4cc18000c007cf9c

def z313 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xe027ffff00000000 0xffc04ffffe000000

def z314 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0xffffe07f00000000 0xc3ffffc0fe000000

def z315 : W := mkw 0x568020a131ab5e82 0x30ad0041426356bd 0xb540619333ffffff 0xf76a80c32667ffff

def z316 : W := mkw 0x0002085000000010 0x02000410a0000000 0xe3c618700007c04f 0x5dc78c30e0000f80

def z317 : W := mkw 0x509d758b3089128a 0x14a13aeb16611225 0x1c39e78f30183190 0xa23873cf1e603063

def z318 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1d580780fc013055 0x343ab00f01f80260

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0xa540001000993ff5 0xf74a80002001327f

def z320 : W := mkw 0x8000800082100004 0x0100010001042000 0x6001800003180020 0x02c0030000063000

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x6021806c00000000 0xc2c04300d8000000

def z322 : W := mkw 0x8000800082100004 0x0100010001042000 0x00000000c3180033 0x0000000001863000

def z323 : W := mkw 0x81008204c2142144 0x8102010409842842 0x0ce1860cc01e31d3 0xae19c30c19803c63

def z324 : W := mkw 0x0202085000204410 0x22040410a0004088 0x000018100001c600 0x100000302000038c

def z325 : W := mkw 0xc580a025a39a0bc6 0x118b01404b473417 0xe021e07f03980fa0 0xc3c043c0fe07301f

def z326 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c618700007ce40 0x5dc78c30e0000f9c

def z327 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x000018600006c000 0x08000030c0000d80

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fd81800fc07c05f 0x1c3fb03001f80f80

def z329 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x08198000cc000000 0x0010330001980000

def z330 : W := mkw 0x50802281708d3282 0x90a1004502e11a65 0xbdc06793f09f3ff7 0xff7b80cf27e13e7f

def z331 : W := mkw 0x0000020040042000 0x8000000400800840 0x0cc00600c0063053 0x2c19800c01800c60

def z332 : W := mkw 0x5000208030891002 0x00a0004100611220 0xb540618030993075 0x376a80c300613260

def z333 : W := mkw 0xf095e081bad91287 0x15e12bc10375b225 0xffdfe193fff9063f 0x13ffbfc327fff20c

def z334 : W := mkw 0x1e0a1ff05527fc10 0xe23c143fe0aa4ff8 0xe3c61ff003e7fe6f 0x7dc78c3fe007cffc

def z335 : W := mkw 0x9d0897a4d717b944 0xc13a112f49ae2f72 0x6ce19fecc31ff9f3 0xfed9c33fd9863ff3

def z336 : W := mkw 0x8500802483120944 0x010a010049062412 0x6ce1866c031809a0 0xeed9c30cd8063013

def z337 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x24400000c31e39f3 0xe648800001863c73

def z338 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0xffffe78f00000000 0xa3ffffcf1e000000

def z339 : W := mkw 0x0000000000000000 0x0000000000000000 0x1540000030000015 0x002a800000600000

def z340 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xffde1870ffe7ce7f 0x5dffbc30e1ffcf9c

def z341 : W := mkw 0x9d0897a4d717b944 0xc13a112f49ae2f72 0x1fd81f80ff1ff9ff 0x3c3fb03f01fe3ff3

def z342 : W := mkw 0x5080208130891282 0x10a1004102611225 0x0000019330993ff5 0xf40000032661327f

def z343 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x4ce1866cc3063053 0x2c99c30cd9860c60

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x60c0000003000023 0x00c1800000060000

def z345 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x8306187000e7ce4c 0x5d060c30e001cf9c

def z346 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0x931e799300e1c60c 0x11263cf32601c38c

def z347 : W := mkw 0x6217685028e84413 0x26c42ed0a051d088 0x931e78103ce1c60c 0x11263cf02079c38c

def z348 : W := mkw 0x1000008010011000 0x0020000100200220 0x35400180301939f5 0xf66a800300603273

def z349 : W := mkw 0x061f5d7a01224c18 0x260c3ebaf4024498 0xebff9e7c03e7ce6f 0x5dd7ff3cf807cf9c

def z350 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xffde1f80ffe7f07f 0x3dffbc3f01ffcfe0

def z351 : W := mkw 0x180a1fda5405b018 0xc230143fb4a80b60 0x00201fff0007f040 0xfc00403ffe000fe0

def z352 : W := mkw 0x0008150000000000 0x0000102a00000000 0xbfd87f9300000000 0xff7fb0ff26000000

def z353 : W := mkw 0xf095e081bad91287 0x15e12bc10375b225 0x1c19e183fc183190 0xa23833c307f83063

def z354 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0x6ce19fff00000000 0xfed9c33ffe000000

def z355 : W := mkw 0x4080200120880282 0x1081004002411005 0xa140601300990fe5 0xd74280c02601321f

def z356 : W := mkw 0x168208f111235e90 0x322d0411e22246bd 0x000019f30007ffc0 0xfc000033e6000fff

def z357 : W := mkw 0x99089784d615b144 0xc132112f09ac2b62 0x1ff99f8cfc1ff1df 0xbe3ff33f19f83fe3

def z358 : W := mkw 0x109f5ddb10011298 0x16213ebbb6200225 0xffffffff00013fc0 0xfffffffffe00027f

def z359 : W := mkw 0x0002085000000010 0x02000410a0000000 0xe3c6187000000000 0x5dc78c30e0000000

def z360 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x5fff9fec00000000 0x3cbfff3fd8000000

def z361 : W := mkw 0x5888358134899282 0x50b1106b02691325 0xb75879933c99fffd 0xf76eb0f3267933ff

def z362 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9540619330813655 0x352a80c32661026c

def z363 : W := mkw 0x8000800082100004 0x0100010001042000 0x6cc18000c31839f3 0xe6d9830001863073

def z364 : W := mkw 0x4080200120880282 0x1081004002411005 0xb540619300980fa0 0xf76a80c32601301f

def z365 : W := mkw 0x87028a74c3366d54 0xa30e0514e9866cda 0x6ce19e7cc31ffff3 0xfed9c33cf9863fff

def z366 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00810e65 0xfffffffffe01021c

def z367 : W := mkw 0x8500802483120944 0x010a010049062412 0x4021806c03000000 0x00804300d8060000

def z368 : W := mkw 0x509f7ddb3089129a 0x16a13efbb6611225 0xffffffff30810604 0xfffffffffe61020c

def z369 : W := mkw 0xf81fffdafeddb01f 0xc7f03fffb5fdbb60 0xfffffffffffff07f 0xffffffffffffffe0

def z370 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540600030993ff5 0x036a80c00061327f

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x0440000000003051 0x2408800000000060

def z372 : W := mkw 0x4000200020880002 0x0080004000411000 0xa000600000980020 0x034000c000013000

def z373 : W := mkw 0x1000008010011000 0x0020000100200220 0xb540019030813e75 0x756a80032061027c

def z374 : W := mkw 0x1808158014019000 0x4030102b00280320 0x175819803c01f05d 0x342eb033007803e0

def z375 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xdb9fe000ffe0000e 0x01b73fc001ffc000

def z376 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x03c01800fc07f05f 0x1c07803001f80fe0

def z377 : W := mkw 0x1008158010011000 0x0020102b00200220 0x1fd81f8030013055 0x3c3fb03f00600260

def z378 : W := mkw 0x850a9f7ec316295c 0x830a153efd862c52 0x6ce19fffc31e39f3 0xfed9c33fff863c73

def z379 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x6edf8000cf78003b 0x02ddbf00019ef000

def z380 : W := mkw 0x0015400000000000 0x04002a8000000000 0x1c19e00000000000 0x023833c000000000

def z381 : W := mkw 0x8015c00082100004 0x05002b8001042000 0xffdfe000c3180033 0x03ffbfc001863000

def z382 : W := mkw 0x87028a74c3366d54 0xa30e0514e9866cda 0x6ee79e6cc37ef9fb 0xeeddcf3cd986fdf3

def z383 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1000618330000000 0x002000c306600000

def z384 : W := mkw 0x8702887483324d54 0x230e0510e906649a 0xe3e7987c03ffcfef 0xdfc7cf30f807ff9f

def z385 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfffffffffc00001f 0xfffffffffff80000

def z386 : W := mkw 0x851fdf7ec316295c 0x870a3fbefd862c52 0x4abf9e6cc3060002 0x08957f3cd9860c00

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x028018000006c00a 0x0805003000000d80

def z388 : W := mkw 0x000a1d5000000010 0x0200143aa0000000 0xffde1ff000000000 0x7dffbc3fe0000000

def z389 : W := mkw 0x81008204c2142144 0x8102010409842842 0x00000000c0183190 0x0000000001803063

def z390 : W := mkw 0x0202085000204410 0x22040410a0004088 0x020618000060c008 0x00040c300000c180

def z391 : W := mkw 0x0080000100000280 0x1001000002000005 0x0000001300000f80 0xc00000002600001f

def z392 : W := mkw 0x181d578a5405b008 0xc4303aaf14a80b60 0x1ff9ff8ffc07f05f 0xbe3ff3ff1ff80fe0

def z393 : W := mkw 0x509d758b3089128a 0x14a13aeb16611225 0xbd79e79f30993ff5 0xf77af3cf3e61327f

def z394 : W := mkw 0x1080008110011280 0x1021000102200225 0x0000018300003180 0xa000000306000063

def z395 : W := mkw 0x4080200120880282 0x1081004002411005 0x8000601300800600 0x010000c02601000c

def z396 : W := mkw 0xd580a2a5f39f3bc6 0x91ab01454be73e77 0x00000000f39f3ff7 0x0000000001e73e7f

def z397 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x7ff99fecfc07f05f 0xfefff33fd9f80fe0

def z398 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0x00001f930007ffc0 0xfc00003f26000fff

def z399 : W := mkw 0x8400802083120804 0x0108010041062410 0x6cc18060c31e0873 0x4ed98300c1863c10

def z400 : W := mkw 0xa01fdd5a8a50001d 0x07403fbab514a000 0xffffffffcf60000a 0xffffffffff9ec000

def z401 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe0c6007003e60e63 0x4dc18c00e007cc1c

def z402 : W := mkw 0xc500a224e39e2946 0x818a014449c73c52 0xfde1e66cf39e39f7 0xeffbc3ccd9e73c73

def z403 : W := mkw 0x0002085000000010 0x02000410a0000000 0x8306181000000000 0x11060c3020000000

def z404 : W := mkw 0x0000020040042000 0x8000000400800840 0x6ce1866cc0063053 0xeed9c30cd9800c60

def z405 : W := mkw 0x548020a1318b1a82 0x10a9004142631635 0xf5c061f3339f3ff7 0xffeb80c3e6673e7f

def z406 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1c180780fc07f05f 0x2038300f01f80fe0

def z407 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x4286186003e7ce6f 0x08850c30c007cf9c

def z408 : W := mkw 0xe01ffd5aaad8001f 0x07c03ffab555b000 0xfffffffffc180010 0xfffffffffff83000

def z409 : W := mkw 0x158002a551073bc0 0x902b00054aa20e77 0x002007ff00073fc0 0xfc00400ffe000e7f

def z410 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1f181f80fc01f01c 0x303e303f01f803e0

def z411 : W := mkw 0x06020a7041266c10 0xa20c0414e0824cd8 0xefc61e70c3e7fe7f 0x7ddf8c3ce187cffc

def z412 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x021e180000000000 0x00043c3000000000

def z413 : W := mkw 0xd080a081b2991286 0x11a1014103653225 0xfdc1e193f3993ff7 0xf7fb83c327e7327f

def z414 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xdbbfffff00000000 0x19b77ffffe000000

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0xa140001000000000 0x5542800020000000

def z416 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x0839860c00000000 0x0010730c18000000

def z417 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0020066cc31e39f3 0xec00400cd9863c73

def z418 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xf3de79f300000000 0x5de7bcf3e6000000

def z419 : W := mkw 0x0202085000204410 0x22040410a0004088 0xe3c6181003e1c62f 0x11c78c302007c38c

def z420 : W := mkw 0x0000020040042000 0x8000000400800840 0x0000060000063040 0x2c00000c00000c60

def z421 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6186003e6c02f 0x09c78c30c007cd80

def z422 : W := mkw 0x0600002001224c00 0x200c000040024498 0x000000000366c00a 0x000000000006cd80

def z423 : W := mkw 0x1e0002a05527fc00 0xe03c000540aa4ff8 0x00000000ffe7fe7f 0x0000000001ffcffc

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000601300000000 0xc34000c026000000

def z425 : W := mkw 0x061f5d7a01224c18 0x260c3ebaf4024498 0xffffffff0366c00a 0xfffffffffe06cd80

def z426 : W := mkw 0xe217e850aaf84417 0x27c42fd0a155f088 0xffdff810fff9c63f 0x13ffbff021fff38c

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a980000cc00000a 0x0015300001980000

def z428 : W := mkw 0x4080200120880282 0x1081004002411005 0x0000000000980fa0 0x000000000001301f

def z429 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0x4027806c00000000 0x00804f00d8000000

def z430 : W := mkw 0x0015400000000000 0x04002a8000000000 0x931e600000000000 0x01263cc000000000

def z431 : W := mkw 0x1c0817a05507b800 0xc038102f40aa0f70 0x7fd81fe0ff07f87f 0x7cffb03fc1fe0ff0

def z432 : W := mkw 0x1e1f5ffa5527fc18 0xe63c3ebff4aa4ff8 0xffffffffffe7fe7f 0xffffffffffffcffc

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0x131800003c00000c 0x0026300000780000

def z434 : W := mkw 0x1080008110011280 0x1021000102200225 0x2440019300193ff1 0xf64880032600327f

def z435 : W := mkw 0x0400002001020800 0x0008000040020410 0x64c00060031e39f3 0xeec98000c0063c73

def z436 : W := mkw 0x509f7ddb3089129a 0x16a13efbb6611225 0xffffffff30183190 0xfffffffffe603063

def z437 : W := mkw 0x409f7d5b2088029a 0x16813efab6411005 0xffffffff00980fa0 0xfffffffffe01301f

def z438 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x13181f803c07f04c 0x3c26303f00780fe0

def z439 : W := mkw 0xe115e204eadc2147 0x85c22bc409d5b842 0x1c39e60cfc183190 0xa23873cc19f83063

def z440 : W := mkw 0xf81df780feddb007 0xc5f03bef01fdbb60 0xffdfe780fff8303f 0x23ffbfcf01fff060

def z441 : W := mkw 0x0002085000000010 0x02000410a0000000 0x0000187000000000 0x5c000030e0000000

def z442 : W := mkw 0x8517c87e8312095c 0x070a2f90fd062412 0xe027e07f031809a0 0xc3c04fc0fe063013

def z443 : W := mkw 0xe01df50aaad8000f 0x05c03bea1555b000 0xffffe78ffff8003f 0xa3ffffcf1ffff000

def z444 : W := mkw 0x851fdf7ec316295c 0x870a3fbefd862c52 0x6eff9e6cc31e39f3 0xeeddff3cd9863c73

def z445 : W := mkw 0x58883781748db282 0xd0b1106f02e91b65 0x1fd81f80fc9fffff 0x3c3fb03f01f93fff

def z446 : W := mkw 0x1080008110011280 0x1021000102200225 0xa140019300813fe5 0xf54280032601027f

def z447 : W := mkw 0xf09ffddbbad9129f 0x17e13ffbb775b225 0xfffffffffff93fff 0xfffffffffffff27f

def z448 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0x101860003c000000 0x002030c000780000

def z449 : W := mkw 0x58802281748db282 0xd0b1004502e91b65 0x00000000fc9fffff 0x0000000001f93fff

def z450 : W := mkw 0x0002085000000010 0x02000410a0000000 0xe006007000000000 0x41c00c00e0000000

def z451 : W := mkw 0x1000008010011000 0x0020000100200220 0x1100018030010004 0x1022000300600200

def z452 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x9fde7f9300000000 0x3d3fbcff26000000

def z453 : W := mkw 0x0500022441062940 0x800a000448820c52 0x0020066c00060000 0x0800400cd8000c00

def z454 : W := mkw 0x0100020440042140 0x8002000408800842 0x0020060c00003180 0xa000400c18000063

def z455 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x8306181003e7ce6f 0x11060c302007cf9c

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fd8000000000000 0x003fb00000000000

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000fc00001f 0x0000000001f80000

def z458 : W := mkw 0x0500022441062940 0x800a000448820c52 0x6ce1866c000639c0 0xeed9c30cd8000c73

def z459 : W := mkw 0xf697e8f1bbfb5e97 0x37ed2fd1e377f6bd 0xffdff9f3ffffffff 0xffffbff3e7ffffff

def z460 : W := mkw 0x81008204c2142144 0x8102010409842842 0x6ce1860cc31831b3 0xa2d9c30c19863063

def z461 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x00000000c3060002 0x0000000001860c00

def z462 : W := mkw 0xf095e081bad91287 0x15e12bc10375b225 0xffdfe000fff93fff 0x03ffbfc001fff27f

def z463 : W := mkw 0x4000200020880002 0x0080004000411000 0xb540619330980035 0xf76a80c326613000

def z464 : W := mkw 0x1000008010011000 0x0020000100200220 0x1400018030003010 0x2028000300600060

def z465 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x1c39ffff00000000 0xfe3873fffe000000

def z466 : W := mkw 0x0e0a1f704526ec10 0xe21c143ee08a4dd8 0xebde1e70cfe7ce6f 0x5dd7bc3ce19fcf9c

def z467 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0c21860cc31e39f3 0xa218430c19863c73

def z468 : W := mkw 0x181f5fda5405b018 0xc6303ebfb4a80b60 0xffffffff0007f040 0xfffffffffe000fe0

def z469 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffdff99300000000 0x13ffbff326000000

def z470 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x15400180fc07f05f 0x342a800301f80fe0

def z471 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdff800ffffc07f 0x1fffbff001ffff80

def z472 : W := mkw 0x2015400008400001 0x04402a8000108000 0x021e00000c600008 0x00043c000018c000

def z473 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x1c19e000fff8003f 0x023833c001fff000

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400618300000000 0xa22800c306000000

def z475 : W := mkw 0x4000200020880002 0x0080004000411000 0xf7c6600033f8003f 0x03ef8cc00067f000

def z476 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe286187003e6ce2a 0x49c50c30e007cd9c

def z477 : W := mkw 0x1000028050053000 0x8020000500a00a60 0x1dc00780f0073057 0x3c3b800f01e00e60

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000019300000000 0xf400000326000000

def z479 : W := mkw 0xe602a870abfa4c17 0x23cc0550e157f498 0xe3c61870ffffce7f 0x5dc78c30e1ffff9c

def z480 : W := mkw 0x1a0a1fd05425f410 0xe234143fa0a84be8 0x9fde1f90fce7f65f 0x3d3fbc3f21f9cfec

def z481 : W := mkw 0x4682287121aa4e92 0x328d0450e243549d 0xe3c6787303ffcfef 0xdfc78cf0e607ff9f

def z482 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb100619330990fa4 0xd36200c32661321f

def z483 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0xffdfe000cf60000a 0x03ffbfc0019ec000

def z484 : W := mkw 0x5080208130891282 0x10a1004102611225 0x2440000030993ff5 0xe64880000061327f

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0x0140000000010045 0x1402800000000200

def z486 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xefe7866cc3fe39ff 0xefdfcf0cd987fc73

def z487 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0xf567e1ff00000000 0xf7eacfc3fe000000

def z488 : W := mkw 0x001f5f5a40042018 0x86003ebeb4800840 0xffffffffc0063053 0xffffffffff800c60

def z489 : W := mkw 0x9d0897a4d717b944 0xc13a112f49ae2f72 0x5ff99fecff07f05f 0x3cbff33fd9fe0fe0

def z490 : W := mkw 0xb81dd780de55b005 0xc5703baf01bcab60 0x5fdf9f80ff67f05f 0x3cbfbf3f01fecfe0

def z491 : W := mkw 0x0400002001020800 0x0008000040020410 0x0000006000060840 0x4c000000c0000c10

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cc00000c0000013 0x0019800001800000

def z493 : W := mkw 0x080817004404a000 0xc010102e00880940 0x1fd81f80cc06c00a 0x3c3fb03f01980d80

def z494 : W := mkw 0xe617e870abfa4c17 0x27cc2fd0e157f498 0xe3c7f87003ffce6f 0x5fc78ff0e007ff9c

def z495 : W := mkw 0x8702887483324d54 0x230e0510e906649a 0xe027807c03f80fa0 0xc3c04f00f807f01f

def z496 : W := mkw 0x601f7d5a28c8001b 0x06c03efab4519000 0x931e79933ce0000c 0x11263cf32679c000

def z497 : W := mkw 0x4080200120880282 0x1081004002411005 0xb540601330980fb5 0xc36a80c02661301f

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z499 : W := mkw 0x528228d130a95692 0x32a50451a26152ad 0x9306799330e1c60c 0x11260cf32661c38c

def z500 : W := mkw 0x4602287021aa4c12 0x228c0450e0435498 0xf7c6787033ffce7f 0x5fef8cf0e067ff9c

def z501 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31e0033 0x0ad9c30cd9863c00

def z502 : W := mkw 0xf080a081bad91287 0x11e101410375b225 0xb5406193fff93fff 0xf76a80c327fff27f

def z503 : W := mkw 0x0500022441062940 0x800a000448820c52 0x0ce0066cc00639d3 0xec19c00cd9800c73

def z504 : W := mkw 0x0000020040042000 0x8000000400800840 0x1fd80600fc06305f 0x2c3fb00c01f80c60

def z505 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0xece7e67f00000000 0xefd9cfccfe000000

def z506 : W := mkw 0xa00080008a500005 0x014001000114a000 0x00000000cf60000a 0x00000000019ec000

def z507 : W := mkw 0x1e020af05527fc10 0xe23c0415e0aa4ff8 0xe3c61870ffe7fe7f 0x5dc78c30e1ffcffc

def z508 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003e00e20 0x5dc78c30e007c01c

def z509 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0xb5406000fff8003f 0x036a80c001fff000

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x2440000000180031 0x0248800000003000

def z511 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0000078000003000 0x2000000f00000060

def z512 : W := mkw 0x8000800082100004 0x0100010001042000 0x7fd98000ff18003f 0x02ffb30001fe3000

def z513 : W := mkw 0xc000a000a2980006 0x0180014001453000 0xfdc1e000f3980037 0x03fb83c001e73000

def z514 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xe007e01303f80fa0 0xc3c00fc02607f01f

def z515 : W := mkw 0x4000200020880002 0x0080004000411000 0xb540601030990e75 0x576a80c02061321c

def z516 : W := mkw 0x569f7dfb31ab5e9a 0x36ad3efbf66356bd 0xffffffff33ffffff 0xfffffffffe67ffff

def z517 : W := mkw 0x1000008010011000 0x0020000100200220 0x17c019803007f05f 0x3c2f803300600fe0

def z518 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0x8006601300000000 0x01000cc026000000

def z519 : W := mkw 0x0015400000000000 0x04002a8000000000 0x4a9f800000000000 0x00953f0000000000

def z520 : W := mkw 0x1080008110011280 0x1021000102200225 0x1540019330013fd5 0xf42a80032660027f

def z521 : W := mkw 0x1808158014019000 0x4030102b00280320 0x101801803c000000 0x0020300300780000

def z522 : W := mkw 0x0002085000000010 0x02000410a0000000 0xefe79e7c00000000 0xffdfcf3cf8000000

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0xa3c018100087ce6f 0x5d47803020010f9c

def z524 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0x1fd80000fff8003f 0x003fb00001fff000

def z525 : W := mkw 0x0002085000000010 0x02000410a0000000 0xe3c6187003e0002f 0x5dc78c30e007c000

def z526 : W := mkw 0xa617c8708b724c15 0x274c2f90e116e498 0xebdf9870cfe7ce6f 0x5dd7bf30e19fcf9c

def z527 : W := mkw 0x4000200020880002 0x0080004000411000 0xb5406000309839f5 0xe76a80c000613073

def z528 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x60c018700307ce63 0x5cc18030e0060f9c

def z529 : W := mkw 0x7095608138c91283 0x14e12ac102719225 0xb75e61933cf93ffd 0xf76ebcc32679f27f

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000001839f1 0x0000000000003073

def z531 : W := mkw 0x4000200020880002 0x0080004000411000 0x0000000030980035 0x0000000000613000

def z532 : W := mkw 0x1a0a1dd01421d410 0x6234143ba02843a8 0x931e19903ce1c60c 0x11263c332079c38c

def z533 : W := mkw 0x181f5dda14019018 0x46303ebbb4280320 0xffffffff3c01c00c 0xfffffffffe780380

def z534 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x6eff9e6c00000000 0xeeddff3cd8000000

def z535 : W := mkw 0x1080008110011280 0x1021000102200225 0x0000019300010600 0x100000032600020c

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000001809a0 0xc240000000003013

def z537 : W := mkw 0x041f5d7a01020818 0x06083ebaf4020410 0xffffffff03060863 0xfffffffffe060c10

def z538 : W := mkw 0x401f7d5a2088001a 0x06803efab4411000 0xffffffff30980035 0xfffffffffe613000

def z539 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9100619330813fc4 0xf52200c32661027f

def z540 : W := mkw 0xe500a224ebde2947 0x81ca014449d7bc52 0x00000000fffe39ff 0x0000000001fffc73

def z541 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x0000187003e7ce6f 0x5c000030e007cf9c

def z542 : W := mkw 0xe717ea74ebfe6d57 0xa7ce2fd4e9d7fcda 0xfffffe7cffffffff 0xfffffffcf9ffffff

def z543 : W := mkw 0x0000020040042000 0x8000000400800840 0x08800600c0060002 0x0811000c01800c00

def z544 : W := mkw 0x8500802483120944 0x010a010049062412 0x6ce1806cc31809b3 0xc2d9c300d9863013

def z545 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd87f93fc07f05f 0xff7fb0ff27f80fe0

def z546 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1540018030993ff5 0x342a80030061327f

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c0180000000000 0x1c07803000000000

def z548 : W := mkw 0x8500802483120944 0x010a010049062412 0x00000000031809a0 0x0000000000063013

def z549 : W := mkw 0x8000800082100004 0x0100010001042000 0x6ce1866cc3180033 0xeed9c30cd9863000

def z550 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x43c618600367c04f 0x1c878c30c006cf80

def z551 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0xf3de60003fe0002f 0x01e7bcc0007fc000

def z552 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x933e7fff00000000 0xfd267cfffe000000

def z553 : W := mkw 0x0400022041062800 0x8008000440820c50 0x6cc00660c3063873 0x6cd9800cc1860c70

def z554 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1cd80780fc063053 0x2c39b00f01f80c60

def z555 : W := mkw 0x568228f131ab5e92 0x32ad0451e26356bd 0xb54079f3309ffff5 0xff6a80f3e6613fff

def z556 : W := mkw 0x1000008010011000 0x0020000100200220 0x0000018000013040 0x3400000300000260

def z557 : W := mkw 0x1808158014019000 0x4030102b00280320 0x1fd81980fc01c01f 0x103fb03301f80380

def z558 : W := mkw 0x001d550000000000 0x04003aaa00000000 0xffdfff8000000000 0x3fffbfff00000000

def z559 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1400618330993ff5 0xa22800c30661327f

def z560 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc003010 0x3c3fb03f01f80060

def z561 : W := mkw 0xc580a225e39e2bc6 0x918b01444bc73c57 0xece1e67fc39e3ff3 0xefd9c3ccff873c7f

def z562 : W := mkw 0x0015400000000000 0x04002a8000000000 0xffffe66c00000000 0xefffffccd8000000

def z563 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0x8006600000e00000 0x01000cc00001c000

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3c6001003e10e6f 0x55c78c002007c21c

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0xb540600000000000 0x036a80c000000000

def z566 : W := mkw 0xf808b780feddb007 0xc1f0116f01fdbb60 0x1fd81f80fffff07f 0x3c3fb03f01ffffe0

def z567 : W := mkw 0x0e0a1f704526ec10 0xe21c143ee08a4dd8 0x4a9e1e60cf66c00a 0x08953c3cc19ecd80

def z568 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff839ff 0xe7ffbfc001fff073

def z569 : W := mkw 0x0617487a01224c18 0x260c2e90f4024498 0xe027e07f03e00e20 0xc3c04fc0fe07c01c

def z570 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0xe3e7f87f00000000 0xdfc7cff0fe000000

def z571 : W := mkw 0x58883781748db282 0xd0b1106f02e91b65 0x1fd87f83fc1ff1df 0xbe3fb0ff07f83fe3

def z572 : W := mkw 0xe51fff7eebde295f 0x87ca3ffefdd7bc52 0xfffffffffffe39ff 0xfffffffffffffc73

def z573 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0xffffffff00e1c60c 0xfffffffffe01c38c

def z574 : W := mkw 0xa617c8708b724c15 0x274c2f90e116e498 0x4a9f9860cf66c00a 0x08953f30c19ecd80

def z575 : W := mkw 0xe515e024abda0947 0x05ca2bc04957b412 0xe027e06c03f809a0 0xc3c04fc0d807f013

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000810e65 0x000000000001021c

def z577 : W := mkw 0x87028a74c3366d54 0xa30e0514e9866cda 0xe3c61870c3ffffff 0x5dc78c30e187ffff

def z578 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330183190 0xf76a80c326603063

def z579 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x03c01f800007f04f 0x3c07803f00000fe0

def z580 : W := mkw 0xf81df580bed99007 0x45f03beb017db320 0xffdff980fff9c03f 0x13ffbff301fff380

def z581 : W := mkw 0x0400002001020800 0x0008000040020410 0xe3c6006003e6086f 0x4dc78c00c007cc10

def z582 : W := mkw 0x0500022441062940 0x800a000448820c52 0x2460066c001e39f1 0xee48c00cd8003c73

def z583 : W := mkw 0x5088358130891282 0x10a1106b02611225 0xbfd87f9330993ff5 0xff7fb0ff2661327f

def z584 : W := mkw 0x061f5d7a01224c18 0x260c3ebaf4024498 0xf3de79f303e7ce6f 0x5de7bcf3e607cf9c

def z585 : W := mkw 0x181d57805405b000 0xc4303aaf00a80b60 0xffdfff80fc07f05f 0x3fffbfff01f80fe0

def z586 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x1fd9e000fc18001f 0x023fb3c001f83000

def z587 : W := mkw 0xe515e224ebde2947 0x85ca2bc449d7bc52 0x7cf9e66cff1e39f3 0xeef9f3ccd9fe3c73

def z588 : W := mkw 0x1d0817a45507b940 0xc03a102f48aa0f72 0x1ff81fecfc07f9df 0xfc3ff03fd9f80ff3

def z589 : W := mkw 0xe515e224ebde2947 0x85ca2bc449d7bc52 0xffdfe000fffe39ff 0x03ffbfc001fffc73

def z590 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0x1ff81fff00000000 0xfc3ff03ffe000000

def z591 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x62c618600366c86b 0x4cc58c30c006cd90

def z592 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x3fd81f80fc1ff9ff 0xfe7fb03f01f83ff3

def z593 : W := mkw 0x0002085000000010 0x02000410a0000000 0x4286186000000000 0x08850c30c0000000

def z594 : W := mkw 0x060a1d7a01224c18 0x220c143af4024498 0xe3e61fff03e7ce6f 0xfdc7cc3ffe07cf9c

def z595 : W := mkw 0x1808158014019000 0x4030102b00280320 0x13d819803c07c04f 0x1c27b03300780f80

def z596 : W := mkw 0x0202085000204410 0x22040410a0004088 0x83c6181000e7c64f 0x1d078c302001cf8c

def z597 : W := mkw 0x081f5f5a4404a018 0xc6103ebeb4880940 0x4abf9e6ccc06c00a 0x08957f3cd9980d80

def z598 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xefe79e7c03e7ce6f 0xffdfcf3cf807cf9c

def z599 : W := mkw 0x8515c224c3162944 0x850a2b8449862c52 0xffffe66cc31e39f3 0xefffffccd9863c73

def z600 : W := mkw 0xa01fdd5a8a50001d 0x07403fbab514a000 0x4abf9e6ccf60000a 0x08957f3cd99ec000

def z601 : W := mkw 0x1080008110011280 0x1021000102200225 0xb540619300013fc0 0xf76a80c32600027f

def z602 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0xebdf8000cfe0002f 0x01d7bf00019fc000

def z603 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x68e1866cc3060863 0x4cd1c30cd9860c10

def z604 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x03c018700007ce4f 0x5c078030e0000f9c

def z605 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd80780fc00301f 0x203fb00f01f80060

def z606 : W := mkw 0xe515e024abda0947 0x05ca2bc04957b412 0xffffe06cfff809bf 0xc3ffffc0d9fff013

def z607 : W := mkw 0xe81df700eedca007 0xc5d03bee01ddb940 0xffdffe00fffec03f 0x0bffbffc01fffd80

def z608 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0xb75e60003cf8003d 0x036ebcc00079f000

def z609 : W := mkw 0x181f5fda5405b018 0xc6303ebfb4a80b60 0x5fff9fecfc07f05f 0x3cbfff3fd9f80fe0

def z610 : W := mkw 0x509f7ddb3089129a 0x16a13efbb6611225 0xb75e799330993ff5 0xf76ebcf32661327f

def z611 : W := mkw 0xf095e081bad91287 0x15e12bc10375b225 0xffdfe183fff831bf 0xa3ffbfc307fff063

def z612 : W := mkw 0x85028a74c3162954 0x830a0514e9862c52 0xefe79e7cc31e39f3 0xffdfcf3cf9863c73

def z613 : W := mkw 0x101f5dda10011018 0x06203ebbb4200220 0xffffffff30013055 0xfffffffffe600260

def z614 : W := mkw 0xf595e2a5fbdf3bc7 0x95eb2bc54bf7be77 0xffffe7ffffff3fff 0xffffffcffffffe7f

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0x000018000007c040 0x1c00003000000f80

def z616 : W := mkw 0x568228f131ab5e92 0x32ad0451e26356bd 0xf54661f333f93ff5 0xf7ea8cc3e667f27f

def z617 : W := mkw 0x81008204c2142144 0x8102010409842842 0x2c61860cc01839f1 0xe658c30c19803073

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000000183190 0xa208000000003063

def z619 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x9f3fff9f00000000 0xb33e7fff3e000000

def z620 : W := mkw 0x0000020040042000 0x8000000400800840 0x2cc00600c01e39f3 0xee59800c01803c73

def z621 : W := mkw 0x8602887083324c14 0x230c0510e1066498 0xefc79870c3ffce7f 0x5fdf8f30e187ff9c

def z622 : W := mkw 0x1080008110011280 0x1021000102200225 0x0000000000013fc0 0x000000000000027f

def z623 : W := mkw 0x1e0a1ff05527fc10 0xe23c143fe0aa4ff8 0x1fd81ff0fc07fe5f 0x7c3fb03fe1f80ffc

def z624 : W := mkw 0x58883781748db282 0xd0b1106f02e91b65 0x9fd87f93fc87f65f 0x3d3fb0ff27f90fec

def z625 : W := mkw 0x9d1fdffed717b95c 0xc73a3fbffdae2f72 0xffffffffff1ff9ff 0xfffffffffffe3ff3

def z626 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb140619330810e65 0x556280c32661021c

def z627 : W := mkw 0x58883781748db282 0xd0b1106f02e91b65 0x1c186783fc183190 0xa23830cf07f83063

def z628 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xb75e799300000000 0xf76ebcf326000000

def z629 : W := mkw 0x0015400000000000 0x04002a8000000000 0xffdfe00003e0002f 0x03ffbfc00007c000

def z630 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330810604 0xf76a80c32661020c

def z631 : W := mkw 0x060a1d7001224c10 0x220c143ae0024498 0xffde1ff003e7ce6f 0x7dffbc3fe007cf9c

def z632 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6021806cc31e39f3 0xc2c04300d9863c73

def z633 : W := mkw 0xe01df500aad80007 0x05c03bea0155b000 0xffdfff80fff8003f 0x3fffbfff01fff000

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x1540018000000000 0x342a800300000000

def z635 : W := mkw 0xf095e081bad91287 0x15e12bc10375b225 0xbd59e193fc993ff5 0xf77ab3c327f9327f

def z636 : W := mkw 0x0617487a01224c18 0x260c2e90f4024498 0xe3e7f87f03e7ce6f 0xdfc7cff0fe07cf9c

def z637 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0xbd79e79f00000000 0xf77af3cf3e000000

def z638 : W := mkw 0x1808158014019000 0x4030102b00280320 0x000019800001c000 0x1000003300000380

def z639 : W := mkw 0x58883781748db282 0xd0b1106f02e91b65 0xb5407f93309ffff5 0xff6a80ff26613fff

def z640 : W := mkw 0x0015400000000000 0x04002a8000000000 0xe007e00000000000 0x03c00fc000000000

def z641 : W := mkw 0xe617e870abfa4c17 0x27cc2fd0e157f498 0xffdfe070fff80e3f 0x43ffbfc0e1fff01c

def z642 : W := mkw 0x8000800082100004 0x0100010001042000 0xefc78000c3f8003f 0x03df8f000187f000

def z643 : W := mkw 0x5888358134899282 0x50b1106b02691325 0x931879933c81c60c 0x112630f32679038c

def z644 : W := mkw 0x8000800082100004 0x0100010001042000 0x48818000c3000002 0x0091030001860000

def z645 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0x00201e6c00000000 0x0800403cd8000000

def z646 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x7ff9866cff1e39ff 0xeefff30cd9fe3c73

def z647 : W := mkw 0x1000008010011000 0x0020000100200220 0x1fd80180fc01305f 0x343fb00301f80260

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cc0060000000000 0x2c19800c00000000

def z649 : W := mkw 0xd782aaf5f3bf7fd6 0xb3af0555ebe77eff 0xffe7fffff3ffffff 0xffffcfffffe7ffff

def z650 : W := mkw 0xd580a0a5b39b1bc6 0x11ab01414b673637 0xf561e1ff33993ff5 0xf7eac3c3fe67327f

def z651 : W := mkw 0x851fdd7e8312095c 0x070a3fbafd062412 0xffffffff031809a0 0xfffffffffe063013

def z652 : W := mkw 0x5080208130891282 0x10a1004102611225 0x0000000030183190 0x0000000000603063

def z653 : W := mkw 0x0600002001224c00 0x200c000040024498 0x03c0180003e7ce6f 0x1c0780300007cf9c

def z654 : W := mkw 0x8500802483120944 0x010a010049062412 0x60e1806c031e09e3 0xcec1c300d8063c13

def z655 : W := mkw 0x950082a4d3173944 0x812a010549a62e72 0x7de187ecf31f39f7 0xfefbc30fd9e63e73

def z656 : W := mkw 0x6617687029ea4c13 0x26cc2ed0e053d498 0xf3de78703fe7ce6f 0x5de7bcf0e07fcf9c

def z657 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x4abf9fff00000000 0xfc957f3ffe000000

def z658 : W := mkw 0x558022a5718f3bc2 0x90ab00454ae31e77 0xb56067ff309f3ff5 0xff6ac0cffe613e7f

def z659 : W := mkw 0x7095608138c91283 0x14e12ac102719225 0x931e61933ce1060c 0x11263cc32679c20c

def z660 : W := mkw 0x4015600020880002 0x04802ac000411000 0xffdfe00030980035 0x03ffbfc000613000

def z661 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0cc01f80c007f053 0x3c19803f01800fe0

def z662 : W := mkw 0x0002085a00000018 0x02000410b4000000 0x0020007f00000000 0xc0004000fe000000

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000001000800e20 0x414000002001001c

def z664 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xe3c7e00003f8002f 0x03c78fc00007f000

def z665 : W := mkw 0x0500022441062940 0x800a000448820c52 0x60e0066c030639e3 0xecc1c00cd8060c73

def z666 : W := mkw 0xdd88b7a5f79fbbc6 0xd1bb116f4bef3f77 0xfff9ffffff9fffff 0xfffff3ffffff3fff

def z667 : W := mkw 0x0600002001224c00 0x200c000040024498 0x000000000007ce40 0x0000000000000f9c

def z668 : W := mkw 0x0617487001224c10 0x260c2e90e0024498 0xffdff87003e7ce6f 0x5fffbff0e007cf9c

def z669 : W := mkw 0x98089780d615b004 0xc130112f01ac2b60 0x7fd99f80ff1ff07f 0x3effb33f01fe3fe0

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x6cc1800000000000 0x02d9830000000000

def z671 : W := mkw 0xf81df780feddb007 0xc5f03bef01fdbb60 0x1fd9ff80fc1ff05f 0x3e3fb3ff01f83fe0

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c180000fc000010 0x0038300001f80000

def z673 : W := mkw 0x9f0a9ff4d737fd54 0xe33e153fe9ae6ffa 0xffff9ffcffffffff 0xffffff3ff9ffffff

def z674 : W := mkw 0x568020a131ab5e82 0x30ad0041426356bd 0x0000000033ffffff 0x000000000067ffff

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0xa140000000800025 0x0142800000010000

def z676 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xe007e000fff8003f 0x03c00fc001fff000

def z677 : W := mkw 0xe017e85aaad8001f 0x07c02fd0b555b000 0xe027e07f03f80020 0xc3c04fc0fe07f000

def z678 : W := mkw 0x0008150000000000 0x0000102a00000000 0x1fd81f800007c04f 0x3c3fb03f00000f80

def z679 : W := mkw 0x8517ca7ec316295c 0x870a2f94fd862c52 0xece7e67fc31e39f3 0xefd9cfccff863c73

def z680 : W := mkw 0x180a1fda5405b018 0xc230143fb4a80b60 0x1ff81ffffc07f05f 0xfc3ff03ffff80fe0

def z681 : W := mkw 0x8500802483120944 0x010a010049062412 0x6461806c031839f1 0xe6c8c300d8063073

def z682 : W := mkw 0x0008150a00000008 0x0000102a14000000 0x0020078f00000000 0xa000400f1e000000

def z683 : W := mkw 0xd580a2a5f39f3bc6 0x91ab01454be73e77 0x7ce1e7eff31e39f3 0xeef9c3cfdfe63c73

def z684 : W := mkw 0x58083780748db002 0xc0b0106f00e91b60 0xbfd87f80fc9ff07f 0x3f7fb0ff01f93fe0

def z685 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe146007003e10e65 0x55c28c00e007c21c

def z686 : W := mkw 0x0400002001020800 0x0008000040020410 0xe1c0007003870e67 0x5dc38000e0070e1c

def z687 : W := mkw 0x0400002001020800 0x0008000040020410 0x0000000003060863 0x0000000000060c10

def z688 : W := mkw 0x508a3ddb3089129a 0x12a1147bb6611225 0xb5607fff30993ff5 0xff6ac0fffe61327f

def z689 : W := mkw 0x8000800082100004 0x0100010001042000 0x0c018000c0180010 0x0218030001803000

def z690 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c618700366c00a 0x5dc78c30e006cd80

def z691 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xea9fe000cff8002a 0x03d53fc0019ff000

def z692 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc3060002 0xeed9c30cd9860c00

def z693 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0cc00600c31e39f3 0x2c19800c01863c73

def z694 : W := mkw 0x5080208130891282 0x10a1004102611225 0x0000000030810604 0x000000000061020c

def z695 : W := mkw 0x4000200020880002 0x0080004000411000 0xbfd86000fc98003f 0x037fb0c001f93000

def z696 : W := mkw 0x051f5f7e41062958 0x860a3ebefc820c52 0xffffffff000639c0 0xfffffffffe000c73

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x03c000000000000f 0x0007800000000000

def z698 : W := mkw 0x1e0a1ff05527fc10 0xe23c143fe0aa4ff8 0x5fde1fe0ff67f05f 0x3cbfbc3fc1fecfe0

def z699 : W := mkw 0xe115e204eadc2147 0x85c22bc409d5b842 0xffffe60cfff831bf 0xa3ffffcc19fff063

def z700 : W := mkw 0x160208f011235c10 0x222c0411e02246b8 0xf7c619f033e7fe7f 0x7def8c33e067cffc

def z701 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0xb5607fff00000000 0xff6ac0fffe000000

def z702 : W := mkw 0x0017485000000010 0x06002e90a0000000 0xffdff87000000000 0x5fffbff0e0000000

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0x030018000001c00c 0x1006003000000380

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3c6180003e7c06f 0x1dc78c300007cf80

def z705 : W := mkw 0xe017e85aaad8001f 0x07c02fd0b555b000 0xffffe07ffff8003f 0xc3ffffc0fffff000

def z706 : W := mkw 0x9d0897a4d717b944 0xc13a112f49ae2f72 0x7cf987ecff1e39f3 0xeef9f30fd9fe3c73

def z707 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xffde0070ffe00e3f 0x41ffbc00e1ffc01c

def z708 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9500619330993fd4 0xf72a00c32661327f

def z709 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd87f83fc07f05f 0xbe3fb0ff07f80fe0

def z710 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xdf9fe000fff8001e 0x03bf3fc001fff000

def z711 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc01e39d0 0xeed9c30cd9803c73

def z712 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffe7ff00000000 0xe3ffffcffe000000

def z713 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xece1e67fc31e39f3 0xefd9c3ccff863c73

def z714 : W := mkw 0x8d008224c716a944 0xc11a0104498e2d52 0x6ce1866ccf1ef9fb 0xeed9c30cd99e3df3

def z715 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x7fd99f80fc07f05f 0x3effb33f01f80fe0

def z716 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc3fe39ff 0xeed9c30cd987fc73

def z717 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xfe9fe000fff8003a 0x03fd3fc001fff000

def z718 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xbd79ffff00000000 0xff7af3fffe000000

def z719 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc07f050 0x3c3fb03f01f80fe0

def z720 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe013fff8003f 0xc3ffbfc027fff000

def z721 : W := mkw 0x0602087a01224c18 0x220c0410f4024498 0xe3e6187f03e7ce6f 0xddc7cc30fe07cf9c

def z722 : W := mkw 0xf81df780feddb007 0xc5f03bef01fdbb60 0xe007ff8003fff060 0x3fc00fff0007ffe0

def z723 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6c21866cc31e39f3 0xe2d8430cd9863c73

def z724 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xf7c679f303ffffff 0xffef8cf3e607ffff

def z725 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x7cf9866cff1e39f3 0xeef9f30cd9fe3c73

def z726 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdff810ffffce7f 0x5fffbff021ffff9c

def z727 : W := mkw 0x5080208130891282 0x10a1004102611225 0xbdc0679330993ff5 0xff7b80cf2661327f

def z728 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xece7866cc3fe39f3 0xefd9cf0cd987fc73

def z729 : W := mkw 0x080817004404a000 0xc010102e00880940 0x1b981e00fc06c00e 0x0837303c01f80d80

def z730 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1400619330993ff5 0xf62800c32661327f

def z731 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0xffffe7ef00000000 0xefffffcfde000000

def z732 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffffe66cfff8003f 0x0bffffccd9fff000

def z733 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00810604 0xfffffffffe01020c

def z734 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xffdfe013fff83fff 0xe7ffbfc027fff07f

def z735 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1e981f80fc07f05f 0x283d303f01f80fe0

def z736 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x13181980fc07c00e 0x1026303301f80f80

def z737 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfcffe7ff00000000 0xeff9ffcffe000000

def z738 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x0206180003e7ce6f 0x00040c300007cf9c

def z739 : W := mkw 0xb095c0819a511285 0x15612b810334a225 0x4a9f8193cf613fca 0xf4953f03279ec27f

def z740 : W := mkw 0x061d552a01224c08 0x240c3aaa54024498 0x1c39e78f03e7ce6f 0xa23873cf1e07cf9c

def z741 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x8306181003e7c60e 0x11060c302007cf8c

def z742 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00010e40 0xfffffffffe00021c

def z743 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff0087ce6f 0xfffffffffe010f9c

def z744 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x1c39ffef00000000 0xaa3873ffde000000

def z745 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xfde1e7ffc39f3ff7 0xfffbc3cfff873e7f

def z746 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x4a9f8000ff78001a 0x00953f0001fef000

def z747 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003ffffff 0x5dc78c30e007ffff

def z748 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xece1867cc39e3ff3 0xefd9c30cf9873c7f

def z749 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0xffffffff00e00600 0xfffffffffe01c00c

def z750 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xebde1870cfe7ce6f 0x5dd7bc30e19fcf9c

def z751 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x48a1866cc31e39f3 0xec91430cd9863c73

def z752 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x7ff99fecfc1ff9ff 0xfefff33fd9f83ff3

def z753 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xebe79e7c03e7ce6f 0x5dd7cf3cf807cf9c

def z754 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfffffffffc07c05f 0xfffffffffff80f80

def z755 : W := mkw 0x9d0895a497139944 0x413a112b492e2732 0x733999ec3f19c9ac 0xd2e67333d87e3393

def z756 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0x6fe19e6cc3ffffff 0xfedfc33cd987ffff

def z757 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xf7c6787003e7ce6f 0x5fef8cf0e007cf9c

def z758 : W := mkw 0x7080208138c91283 0x10e1004102719225 0xb54061933cf93ffd 0xf76a80c32679f27f

def z759 : W := mkw 0x1e8a1ff15527fe90 0xf23d143fe2aa4ffd 0x00001ff30007ffc0 0xfc00003fe6000fff

def z760 : W := mkw 0xe015e00aaad8000f 0x05c02bc01555b000 0xffffe00ffff8003f 0x83ffffc01ffff000

def z761 : W := mkw 0x1e0a1ff05527fc10 0xe23c143fe0aa4ff8 0xfc1e07f0ffe03e30 0x61f83c0fe1ffc07c

def z762 : W := mkw 0x48883701648ca282 0xd091106e02c91945 0xaa987e13cc9ecfaa 0xcb5530fc27993d9f

def z763 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x68e1866cc31e39f3 0x4cd1c30cd9863c73

def z764 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xffde187003e7ce6f 0x5dffbc30e007cf9c

def z765 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xe027e7ff00000000 0xe3c04fcffe000000

def z766 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0a981f80fc07f05f 0x3c15303f01f80fe0

def z767 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6de1866cc31f39f7 0xfedbc30cd9863e73

def z768 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x7fdf8000ff78003f 0x02ffbf0001fef000

def z769 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1f181f80fc07f05f 0x303e303f01f80fe0

def z770 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31e3192 0xeed9c30cd9863c63

def z771 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffffe7fffff8003f 0xffffffcffffff000

def z772 : W := mkw 0x1808178a5405b008 0xc030102f14a80b60 0x1ff81f8ffc07f05f 0xbc3ff03f1ff80fe0

def z773 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xefc61e7003e7ce6f 0x7ddf8c3ce007cf9c

def z774 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00800e20 0xfffffffffe01001c

def z775 : W := mkw 0x5080208130891282 0x10a1004102611225 0xbfd87993fc9fffff 0xff7fb0f327f93fff

def z776 : W := mkw 0x5080208130891282 0x10a1004102611225 0xa000619300983fa0 0xe34000c32601307f

def z777 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xdbbfffff00000000 0xfdb77ffffe000000

def z778 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb400619330993ff5 0xe36800c32661327f

def z779 : W := mkw 0x0702087401224d50 0x220e0410e802449a 0xe3e6187c03e7cfef 0xddc7cc30f807cf9f

def z780 : W := mkw 0x5080208130891282 0x10a1004102611225 0xf7c6799333ffffff 0xffef8cf32667ffff

def z781 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1f181f80fc07f05c 0x3c3e303f01f80fe0

def z782 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x02181800fc07f05f 0x0004303001f80fe0

def z783 : W := mkw 0x509f7ddb3089129a 0x16a13efbb6611225 0x4abf9e6c30993ff5 0x08957f3cd861327f

def z784 : W := mkw 0xf89df781feddb287 0xd5f13bef03fdbb65 0x1c19e783fc183190 0xa23833cf07f83063

def z785 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x1c39e7ff00000000 0xe23873cffe000000

def z786 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x4ca1866cc31e39f3 0xaa99430cd9863c73

def z787 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe193fff8003f 0x13ffbfc327fff000

def z788 : W := mkw 0x5080208130891282 0x10a1004102611225 0xa440619300993ff1 0xf74880c32601327f

def z789 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x5ebfffff00000000 0xfebd7ffffe000000

def z790 : W := mkw 0x080817004404a000 0xc010102e00880940 0x1fd81e00fc06f05f 0x2c3fb03c01f80de0

def z791 : W := mkw 0x1000008010011000 0x0020000100200220 0x1fd81980fc07f05f 0x3c3fb03301f80fe0

def z792 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xfb9fe000fff8002e 0x03f73fc001fff000

def z793 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xfde1e66cc31e39f3 0xeffbc3ccd9863c73

def z794 : W := mkw 0x080817004404a000 0xc010102e00880940 0x1fd81f80fc06c01f 0x3c3fb03f01f80d80

def z795 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6fe1866cc31e39ff 0xeedfc30cd9863c73

def z796 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1ed81f80fc06f05b 0x2c3db03f01f80de0

def z797 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0xffffffff00e1ce6d 0xfffffffffe01c39c

def z798 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0xffffffff0001c600 0xfffffffffe00038c

def z799 : W := mkw 0x83028a54c2346554 0xa3060514a98468ca 0x8f279e1cc0f9f79c 0xb31e4f3c3981f3ef

def z800 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1b981f80fc07f05f 0x1837303f01f80fe0

def z801 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xdfdfe000ffe0001f 0x01bfbfc001ffc000

def z802 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xefc7987003e7ce6f 0x5fdf8f30e007cf9c

def z803 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe010fff93fff 0xf7ffbfc021fff27f

def z804 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0a981e00fc07c00e 0x0815303c01f80f80

def z805 : W := mkw 0xf580a2a5fbdf3bc7 0x91eb01454bf7be77 0x00000000ffff3fff 0x0000000001fffe7f

def z806 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xffff866cfffe39ff 0xefffff0cd9fffc73

def z807 : W := mkw 0x5080208130891282 0x10a1004102611225 0xfde1e7ff30810604 0xfffbc3cffe61020c

def z808 : W := mkw 0x5080208130891282 0x10a1004102611225 0xa000619330993ff5 0xf74000c32661327f

def z809 : W := mkw 0xe000a000aad80007 0x01c001400155b000 0xffde0000fff8003f 0x01ffbc0001fff000

def z810 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x6edf8000fff8003f 0x02ddbf0001fff000

def z811 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x5fde1f80ff67f05f 0x3cbfbc3f01fecfe0

def z812 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6186003e7ce6f 0x09c78c30c007cf9c

def z813 : W := mkw 0x568228f131ab5e92 0x32ad0451e26356bd 0x568679e3337ef19a 0xaaad0cf3c666fde3

def z814 : W := mkw 0x81008204c2142144 0x8102010409842842 0x6ce1866cc01e31d3 0xeed9c30cd9803c63

def z815 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb74079933099fffd 0xf76e80f3266133ff

def z816 : W := mkw 0x5080208130891282 0x10a1004102611225 0x0000619300193fc0 0xf60000c32600327f

def z817 : W := mkw 0xdd80a2a5f79fbbc6 0xd1bb01454bef3f77 0x00000000ff9fffff 0x0000000001ff3fff

def z818 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3e61e7c03e7ce6f 0xfdc7cc3cf807cf9c

def z819 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xffe7ffff03e7ce6f 0xffffcffffe07cf9c

def z820 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff0001c00c 0xfffffffffe000380

def z821 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x4c21866cc3183190 0xa298430cd9863063

def z822 : W := mkw 0xd580a2a5f39f3bc6 0x91ab01454be73e77 0xd9a1e7fff3870606 0x19b343cfffe70e0c

def z823 : W := mkw 0x529f7ddb30a9569a 0x36a53efbb66152ad 0x931e799330e1c60c 0x11263cf32661c38c

def z824 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00180031 0xfffffffffe003000

def z825 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6c21866cc31e39f0 0xeed8430cd9863c73

def z826 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x5e9f8000ff60001a 0x00bd3f0001fec000

def z827 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x7effffef00000000 0xeefdffffde000000

def z828 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0xffffffff0060c008 0xfffffffffe00c180

def z829 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdff800fffec03f 0x0bffbff001fffd80

def z830 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x5fffffef00000000 0xbebfffffde000000

def z831 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff8087f 0x47ffbfc001fff010

def z832 : W := mkw 0x5080208130891282 0x10a1004102611225 0xf561e1ff30993ff5 0xf7eac3c3fe61327f

def z833 : W := mkw 0x6015600028c80003 0x04c02ac000519000 0xffde6000ffe0003f 0x01ffbcc001ffc000

def z834 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x2c61866cc01e39f1 0xee58c30cd9803c73

def z835 : W := mkw 0x6515622469ce2943 0x84ca2ac448d39c52 0x933e666c3ce639cc 0xed267cccd879cc73

def z836 : W := mkw 0xe617e87aabfa4c1f 0x27cc2fd0f557f498 0xe027e07f03f80e20 0xc3c04fc0fe07f01c

def z837 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb7c0619330993fff 0xf76f80c32661327f

def z838 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe286187003e7ce6a 0x5dc50c30e007cf9c

def z839 : W := mkw 0x0000020040042000 0x8000000400800840 0x6ce1866cc01e39f3 0xeed9c30cd9803c73

def z840 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330983fb5 0xe36a80c32661307f

def z841 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x5e9fe000fff8003f 0x02bd3fc001fff000

def z842 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc39f3ff7 0xeed9c30cd9873e7f

def z843 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x4ca1866cc31e39d2 0xee99430cd9863c73

def z844 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xea9fe000fff8003f 0x03d53fc001fff000

def z845 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0x6ce1866cc37ef9fb 0xeed9c30cd986fdf3

def z846 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3e7987c03e7ce6f 0xdfc7cf30f807cf9c

def z847 : W := mkw 0x5080208130891282 0x10a1004102611225 0xbd586193fc993ff5 0xf77ab0c327f9327f

def z848 : W := mkw 0x851fdf7ec316295c 0x870a3fbefd862c52 0x931e7993c31e39f3 0x11263cf327863c73

def z849 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff9007f 0x17ffbfc001fff200

def z850 : W := mkw 0x5080208130891282 0x10a1004102611225 0xf546619333f93ff5 0xf7ea8cc32667f27f

def z851 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1f981f80fc07f01e 0x383f303f01f80fe0

def z852 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x9fde1f80fce7f05f 0x3d3fbc3f01f9cfe0

def z853 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6461866c031e39f1 0xeec8c30cd8063c73

def z854 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xff3fffff00000000 0xf3fe7ffffe000000

def z855 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd81f90fc07f05f 0x7d7fb03f21f80fe0

def z856 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xfbdfe000ffe0002f 0x01f7bfc001ffc000

def z857 : W := mkw 0xe617e870abfa4c17 0x27cc2fd0e157f498 0x1c19f870fc1fce50 0x5e3833f0e1f83f9c

def z858 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330193fd0 0xf76a80c32660327f

def z859 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfbffffff00000000 0x5df7fffffe000000

def z860 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0xffffffff00e7c64f 0xfffffffffe01cf8c

def z861 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe7c6187003e7ce6f 0xffcf8c30e007cf9c

def z862 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb100619330993ff5 0xd36200c32661327f

def z863 : W := mkw 0x0600002001224c00 0x200c000040024498 0xe3c6180003e7ce6f 0x1dc78c300007cf9c

def z864 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00000000 0x1bfffffffe000000

def z865 : W := mkw 0x81008204c2142144 0x8102010409842842 0x6ce1866cc01839f1 0xeed9c30cd9803073

def z866 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe306187003e7ce6c 0x5dc60c30e007cf9c

def z867 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff30000015 0xfffffffffe600000

def z868 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x5abfffef00000000 0x08b57fffde000000

def z869 : W := mkw 0x8500802483120944 0x010a010049062412 0x6ce1866c031839f1 0xeed9c30cd8063073

def z870 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffffe66cfff839ff 0xefffffccd9fff073

def z871 : W := mkw 0x5080208130891282 0x10a1004102611225 0x3440619330193ff1 0xf66880c32660327f

def z872 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff03e10e6f 0xfffffffffe07c21c

def z873 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xf7c619f003e7ce6f 0x7def8c33e007cf9c

def z874 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd81f90fc9fffff 0xff7fb03f21f93fff

def z875 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x5b9f8000ff60000e 0x00b73f0001fec000

def z876 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe180fff8003f 0x37ffbfc301fff000

def z877 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x4286187003e7ce6f 0x5c850c30e007cf9c

def z878 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x5ff99fecfc07f05f 0x3cbff33fd9f80fe0

def z879 : W := mkw 0x81008204c2142144 0x8102010409842842 0x0c21866cc0183190 0xee18430cd9803063

def z880 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x68a1866cc31e39e2 0xeed1430cd9863c73

def z881 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x17581980fc07f05f 0x342eb03301f80fe0

def z882 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff0007c040 0xfffffffffe000f80

def z883 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0021866c001e39c0 0xee00430cd8003c73

def z884 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3c6181003e7ce6f 0x5dc78c302007cf9c

def z885 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff839ff 0x03ffbfc001fff073

def z886 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9100619330993ff5 0xf52200c32661327f

def z887 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff831bf 0xa3ffbfc001fff063

def z888 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc06f01a 0x3c3fb03f01f80de0

def z889 : W := mkw 0xe617e870abfa4c17 0x27cc2fd0e157f498 0xe007e06003f80020 0x03c00fc0c007f000

def z890 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6021866c031839a0 0xe2c0430cd8063073

def z891 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb75861933c993ffd 0xf76eb0c32679327f

def z892 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x8306187003e7ce6f 0x5d060c30e007cf9c

def z893 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x13181f80fc07f05f 0x3c26303f01f80fe0

def z894 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffffc0000013 0xffffffffff800000

def z895 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x3fd81f80fc1ff07f 0x3e7fb03f01f83fe0

def z896 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x931e6000ffe0000e 0x01263cc001ffc000

def z897 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x5fdfe000ff78001f 0x02bfbfc001fef000

def z898 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0xbfd81f93fc87ffff 0xfd7fb03f27f90fff

def z899 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1b981f80fc07f04e 0x3c37303f01f80fe0

def z900 : W := mkw 0x5080208130891282 0x10a1004102611225 0xbd61e79f30993ff5 0xf77ac3cf3e61327f

def z901 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003e7ce60 0x5dc78c30e007cf9c

def z902 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x0021ffff00000000 0xfe0043fffe000000

def z903 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x4ce1866cc31e39f3 0x2c99c30cd9863c73

def z904 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe386187003e7ce2e 0x59c70c30e007cf9c

def z905 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdff800fff8003f 0x1fffbff001fff000

def z906 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619333f93fff 0xf76a80c32667f27f

def z907 : W := mkw 0x0000000000000000 0x0000000000000000 0x7ce1e7ef00000000 0xeef9c3cfde000000

def z908 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xc386187003e7ce4e 0x5d870c30e007cf9c

def z909 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe306187003e7ce6f 0x51c60c30e007cf9c

def z910 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00e0000c 0xfffffffffe01c000

def z911 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xf33fffff00000000 0xffe67ffffe000000

def z912 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x13d81980fc07f05f 0x1c27b03301f80fe0

def z913 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfbbfffff00000000 0xdbf77ffffe000000

def z914 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe060fff8003f 0x4fffbfc0c1fff000

def z915 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31e39f3 0x0ad9c30cd9863c73

def z916 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1867cc31f3ff3 0xfed9c30cf9863e7f

def z917 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0x1fd81f93fc07f65f 0x3c3fb03f27f80fec

def z918 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff0006c00a 0xfffffffffe000d80

def z919 : W := mkw 0x021f5d5a00204418 0x26043ebab4004088 0xffffffff03e1c62f 0xfffffffffe07c38c

def z920 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000ff78001a 0x03ffbfc001fef000

def z921 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xe3e7ffff00000000 0xffc7cffffe000000

def z922 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc06f01f 0x283fb03f01f80de0

def z923 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff000039c0 0xfffffffffe000073

def z924 : W := mkw 0x18174ada5405b018 0xc6302e95b4a80b60 0xe027e07ffc07f05f 0xc3c04fc0fff80fe0

def z925 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003e7c62f 0x19c78c30e007cf8c

def z926 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x1c39e7ef00000000 0xee3873cfde000000

def z927 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xefe7866cc31e39f3 0xefdfcf0cd9863c73

def z928 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd87f80fc07f05f 0x3f7fb0ff01f80fe0

def z929 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce19e6cc31ff9f3 0xfed9c33cd9863ff3

def z930 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xc3c6187003e7c64f 0x1d878c30e007cf8c

def z931 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe006187003e7ce6f 0x5dc00c30e007cf9c

def z932 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x021e0000fff8003f 0x00043c0001fff000

def z933 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe010fff8003f 0x57ffbfc021fff000

def z934 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6021866cc31e39f3 0xeec0430cd9863c73

def z935 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb500619330993fb4 0xf36a00c32661327f

def z936 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ee7866cc37e39fb 0xeeddcf0cd986fc73

def z937 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xefc61870c3e7ce7f 0x5ddf8c30e187cf9c

def z938 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x4a9f8000ffe0000e 0x00953f0001ffc000

def z939 : W := mkw 0xd780a2a5f3bf7fc6 0xb1af01454be77eff 0x00000000f3ffffff 0x0000000001e7ffff

def z940 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1bd81f80fc07c04f 0x1c37b03f01f80f80

def z941 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xffdfe013fff90fff 0xd7ffbfc027fff21f

def z942 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003ffcfef 0xdfc78c30e007ff9f

def z943 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xffde1f80fc07f05f 0x3dffbc3f01f80fe0

def z944 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdff800fff9c03f 0x13ffbff001fff380

def z945 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866c031e39e0 0xeed9c30cd8063c73

def z946 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xefe79e7c03ffffff 0xffdfcf3cf807ffff

def z947 : W := mkw 0x5080208130891282 0x10a1004102611225 0xfdc1e19330993ff5 0xf7fb83c32661327f

def z948 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xf567ffff00000000 0xffeacffffe000000

def z949 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xffdfe000fff80fbf 0x03ffbfc001fff01f

def z950 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x7ff9ffef00000000 0xfefff3ffde000000

def z951 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31839b0 0xeed9c30cd9863073

def z952 : W := mkw 0x5080208130891282 0x10a1004102611225 0xffde6193fff93fff 0xf7ffbcc327fff27f

def z953 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe600fff8003f 0x2fffbfcc01fff000

def z954 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x9fde6000fff8003f 0x013fbcc001fff000

def z955 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xf3c679f303e7ce6f 0x5de78cf3e607cf9c

def z956 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x7cf9ffff00000000 0xfef9f3fffe000000

def z957 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ee19e6cc31ef9fb 0xeeddc33cd9863df3

def z958 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x7fd81fe0fc07f05f 0x7cffb03fc1f80fe0

def z959 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xf3de6000fff8003f 0x01e7bcc001fff000

def z960 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619300993fe0 0xf76a80c32601327f

def z961 : W := mkw 0x0000020040042000 0x8000000400800840 0x1fd81e00fc07f05f 0x3c3fb03c01f80fe0

def z962 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe0c6187003e7ce63 0x5dc18c30e007cf9c

def z963 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb7c0799330993ff5 0xff6f80f32661327f

def z964 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x4ce1866cc31e31d3 0xae99c30cd9863c63

def z965 : W := mkw 0x509f7ddb3089129a 0x16a13efbb6611225 0x931e799330000000 0x11263cf326600000

def z966 : W := mkw 0x5080208130891282 0x10a1004102611225 0xf5c0619333993ff7 0xf7eb80c32667327f

def z967 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ef9866ccf1e39fb 0xeeddf30cd99e3c73

def z968 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xb75e6000fff8003f 0x036ebcc001fff000

def z969 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xfcdfe000fff80033 0x03f9bfc001fff000

def z970 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003e7ffef 0xfdc78c30e007cfff

def z971 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00003051 0xfffffffffe000060

def z972 : W := mkw 0x000a1d5a00000018 0x0200143ab4000000 0xfde1ffff00000000 0xfffbc3fffe000000

def z973 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000ffe0000e 0x03ffbfc001ffc000

def z974 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xf3de18703fe7ce6f 0x5de7bc30e07fcf9c

def z975 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80ffe7f07f 0x3c3fb03f01ffcfe0

def z976 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0ed81e00fc07f05f 0x2c1db03c01f80fe0

def z977 : W := mkw 0xe115e004aad80147 0x05c22bc00955b002 0xffffe00cfff801bf 0x83ffffc019fff003

def z978 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x48a1866cc31e3192 0x0891430cd9863c63

def z979 : W := mkw 0x709f7ddb38c9129b 0x16e13efbb6719225 0x931e79933ce1060c 0x11263cf32679c20c

def z980 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1400619330183f90 0xe22800c32660307f

def z981 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0x1fd81f80fc07ffdf 0x3c3fb03f01f80fff

def z982 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xe3c7f80003ffc06f 0x1fc78ff00007ff80

def z983 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0ce1866cc01e39d3 0xee19c30cd9803c73

def z984 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x7ff9866cc31e39f3 0xeefff30cd9863c73

def z985 : W := mkw 0xe00abd5aaad8001f 0x03c0157ab555b000 0x00201ffffff8003f 0xfc00403ffffff000

def z986 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb100619330993fe4 0xf76200c32661327f

def z987 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xefe7867cc3ff3fff 0xffdfcf0cf987fe7f

def z988 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31839b3 0xe2d9c30cd9863073

def z989 : W := mkw 0x0500022441062940 0x800a000448820c52 0x6ce1866c001e39f1 0xeed9c30cd8003c73

def z990 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330993ff5 0x136a80c32661327f

def z991 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfffffffffc000010 0xfffffffffff80000

def z992 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc87fe7f 0x3c3fb03f01f90ffc

def z993 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc07c00e 0x3c3fb03f01f80f80

def z994 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x7ff99e6cff1ff9ff 0xfefff33cd9fe3ff3

def z995 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb440619330983ff1 0xe76880c32661307f

def z996 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xefe79e6cc3fff9ff 0xffdfcf3cd987fff3

def z997 : W := mkw 0x0400002001020800 0x0008000040020410 0x6ce1866c031e39f3 0xeed9c30cd8063c73

def z998 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0xfdf9e7ff00000000 0xfffbf3cffe000000

def z999 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc1ff1df 0xbe3fb03f01f83fe3

def z1000 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xc386187003e7ce6f 0x19870c30e007cf9c

def z1001 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffffe06cfff8003f 0xc3ffffc0d9fff000

def z1002 : W := mkw 0xa5008224cb562945 0x814a01044996ac52 0x6ce1866ccf7e39fb 0xeed9c30cd99efc73

def z1003 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0x6ce1866cc3fe3ff3 0xeed9c30cd987fc7f

def z1004 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x43c6186003e7ce6f 0x1c878c30c007cf9c

def z1005 : W := mkw 0x080817004404a000 0xc010102e00880940 0x1fd81e00fc07c05f 0x1c3fb03c01f80f80

def z1006 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x1fd81870fc07ce5f 0x5c3fb030e1f80f9c

def z1007 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xfff9fffffc07f05f 0xfffff3fffff80fe0

def z1008 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81e00fc07f05f 0x083fb03c01f80fe0

def z1009 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xa346181003e7ce6f 0x55468c302007cf9c

def z1010 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfc3fffff00000000 0xfff87ffffe000000

def z1011 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xefe19e7cc39fffff 0xffdfc33cf9873fff

def z1012 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc07c01f 0x183fb03f01f80f80

def z1013 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x5cb9e7ef00000000 0xaab973cfde000000

def z1014 : W := mkw 0x5080208130891282 0x10a1004102611225 0x1540619330193fd5 0xf62a80c32660327f

def z1015 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0x1fd81f83fc07f1df 0xbc3fb03f07f80fe3

def z1016 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xb5406193c31e39f3 0xf76a80c327863c73

def z1017 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xece7ffff00000000 0xffd9cffffe000000

def z1018 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff03e7c06f 0xfffffffffe07cf80

def z1019 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9540619330993ff5 0x352a80c32661327f

def z1020 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x9fd87f93fc07f05f 0x3d3fb0ff27f80fe0

def z1021 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00010045 0xfffffffffe000200

def z1022 : W := mkw 0x5080208130891282 0x10a1004102611225 0xbfd8619330993ff5 0xf77fb0c32661327f

def z1023 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0bd81e00fc07f05f 0x1c17b03c01f80fe0

def z1024 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1d581f80fc07f055 0x3c3ab03f01f80fe0

def z1025 : W := mkw 0x081f5d5a04008018 0x46103ebab4080100 0xffffffff0c00c008 0xfffffffffe180180

def z1026 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0xede1867cc3ffffff 0xffdbc30cf987ffff

def z1027 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00993ff5 0xfffffffffe01327f

def z1028 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x5a9fe000ff60000a 0x00b53fc001fec000

def z1029 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xffdfe003fff801bf 0x83ffbfc007fff003

def z1030 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6fe19e6cc31e39f3 0xfedfc33cd9863c73

def z1031 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffffe60cfff8003f 0xa3ffffcc19fff000

def z1032 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe010fff9063f 0x13ffbfc021fff20c

def z1033 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff8307f 0x27ffbfc001fff060

def z1034 : W := mkw 0x0000000000000000 0x0000000000000000 0xb540619300993ff5 0xf76a80c32601327f

def z1035 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xe3c61f8003e7f06f 0x3dc78c3f0007cfe0

def z1036 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb5406193fc993fff 0xf76a80c327f9327f

def z1037 : W := mkw 0x81008204c2142144 0x8102010409842842 0x6ce1866cc31831b3 0xeed9c30cd9863063

def z1038 : W := mkw 0x81008204c2142144 0x8102010409842842 0x6c21866cc0183190 0xe2d8430cd9803063

def z1039 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff03e00020 0xfffffffffe07c000

def z1040 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x7edfe000ff78003b 0x02fdbfc001fef000

def z1041 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x60e1866c031e39e3 0xeec1c30cd8063c73

def z1042 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cff1e39ff 0xeed9c30cd9fe3c73

def z1043 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb5406193309fffff 0xf76a80c326613fff

def z1044 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe193fff839ff 0xf7ffbfc327fff073

def z1045 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fd81800fc06c01f 0x083fb03001f80d80

def z1046 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xfd5fe000fff80035 0x03fabfc001fff000

def z1047 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00000861 0xfffffffffe000010

def z1048 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff0360000a 0xfffffffffe06c000

def z1049 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff0000000f 0xfffffffffe000000

def z1050 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc1ff9ff 0x3c3fb03f01f83ff3

def z1051 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0c21866cc01e3190 0xaa18430cd9803c63

def z1052 : W := mkw 0xe717e874abfa4d57 0x27ce2fd0e957f49a 0xe027e07c03f80fa0 0xc3c04fc0f807f01f

def z1053 : W := mkw 0x080817004404a000 0xc010102e00880940 0x1e981e00fc06c01a 0x083d303c01f80d80

def z1054 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c619f303e7ce6f 0xfdc78c33e607cf9c

def z1055 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x7de1866cf31e39f7 0xeefbc30cd9e63c73

def z1056 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x7fd81f80ff07f07f 0x3cffb03f01fe0fe0

def z1057 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x3fd81f80fc07f05f 0xfe7fb03f01f80fe0

def z1058 : W := mkw 0x1f0a1ff45527fd50 0xe23e143fe8aa4ffa 0x00201ffc0007ffc0 0xfc00403ff8000fff

def z1059 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x9f3fffff00000000 0xff3e7ffffe000000

def z1060 : W := mkw 0x0017485a00000018 0x06002e90b4000000 0xfde7e7ff00000000 0xfffbcfcffe000000

def z1061 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff809bf 0xc3ffbfc001fff013

def z1062 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff90e7f 0x03ffbfc001fff21c

def z1063 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6787303e7ce6f 0xdfc78cf0e607cf9c

def z1064 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb5c06193309f3ff7 0xff6b80c326613e7f

def z1065 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0x4a9f8000ff60001f 0x00953f0001fec000

def z1066 : W := mkw 0x1808158014019000 0x4030102b00280320 0x1fd81980fc07c05f 0x1c3fb03301f80f80

def z1067 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xffde1f90ffe7fe7f 0x7dffbc3f21ffcffc

def z1068 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0x3fd81f93fc1fffff 0xfe7fb03f27f83fff

def z1069 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x0a981e00fc06f01a 0x0815303c01f80de0

def z1070 : W := mkw 0x589f7ddb3489929a 0x56b13efbb6691325 0x931e79933c81c60c 0x11263cf32679038c

def z1071 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x5fdf8000fff8003f 0x00bfbf0001fff000

def z1072 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x4286186003e7c60e 0x08850c30c007cf8c

def z1073 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xebdf8000fff8003f 0x01d7bf0001fff000

def z1074 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ca1866cc31e39b2 0xead9430cd9863c73

def z1075 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0c21866cc31e39f3 0xee18430cd9863c73

def z1076 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce187ffc31e39f3 0xfed9c30fff863c73

def z1077 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0x6ce1866cc31ffff3 0xeed9c30cd9863fff

def z1078 : W := mkw 0x81008204c2142144 0x8102010409842842 0x4ca1866cc0183190 0xaa99430cd9803063

def z1079 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfd7fe7ff00000000 0xf7faffcffe000000

def z1080 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb400619330993ff0 0xf76800c32661327f

def z1081 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe193fff90e7f 0xf7ffbfc327fff21c

def z1082 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb746619330f93ffd 0xf76e8cc32661f27f

def z1083 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x83c6181003e7ce6f 0x1d078c302007cf9c

def z1084 : W := mkw 0x0000000000000000 0x0000000000000000 0x6ce1866c00183190 0xeed9c30cd8003063

def z1085 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xdfffffff00000000 0x3dbffffffe000000

def z1086 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xffdfe193fff80fbf 0xf7ffbfc327fff01f

def z1087 : W := mkw 0x080817004404a000 0xc010102e00880940 0x0a981e00fc06c01f 0x0815303c01f80d80

def z1088 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xede1866cc39e39f7 0xefdbc30cd9873c73

def z1089 : W := mkw 0x188817815405b280 0xd031102f02a80b65 0xbfd87f93fc07ffdf 0xff7fb0ff27f80fff

def z1090 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x9fd81f90fc87f65f 0x3d3fb03f21f90fec

def z1091 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd81f80fc87f07f 0x3d7fb03f01f90fe0

def z1092 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1cd81f80fc07f053 0x3c39b03f01f80fe0

def z1093 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x5c3fe7ef00000000 0xa2b87fcfde000000

def z1094 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6c61866cc31839f1 0xe6d8c30cd9863073

def z1095 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xdb9fe000fff8003f 0x01b73fc001fff000

def z1096 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6181003e7ce6f 0x11c78c302007cf9c

def z1097 : W := mkw 0xe697e871abfa4e97 0x37cd2fd0e357f49d 0xe007e07303f80fa0 0xc3c00fc0e607f01f

def z1098 : W := mkw 0x0008150000000000 0x0000102a00000000 0xfff9ffff00000000 0xfffff3fffe000000

def z1099 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd87f93fc87fe7f 0xff7fb0ff27f90ffc

def z1100 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0xffdfe000ff60001f 0x03ffbfc001fec000

def z1101 : W := mkw 0xe095e001aad80287 0x15c12bc00355b005 0xffdfe013fff8063f 0x03ffbfc027fff00c

def z1102 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xfc1fe000fff8003f 0x03f83fc001fff000

def z1103 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1a981f80fc06c00a 0x0835303f01f80d80

def z1104 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00060043 0xfffffffffe000c00

def z1105 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fffe007f 0x0fffbfc001fffc00

def z1106 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x9f1fe000fff8003f 0x033e3fc001fff000

def z1107 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffffffe0003f 0xffffffffffffc000

def z1108 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x3fd81f80fc07f87f 0x7c7fb03f01f80ff0

def z1109 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f90fc07fe5f 0x7c3fb03f21f80ffc

def z1110 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1ff99f8cfc07f05f 0xbe3ff33f19f80fe0

def z1111 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xeabfffff00000000 0xffd57ffffe000000

def z1112 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xf31fe000fff8003f 0x03e63fc001fff000

def z1113 : W := mkw 0x1080008110011280 0x1021000102200225 0xb540619300193ff1 0xf76a80c32600327f

def z1114 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe146187003e7ce65 0x5dc28c30e007cf9c

def z1115 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x68a1866cc31e39f3 0xcad1430cd9863c73

def z1116 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb56067ff30993ff5 0xff6ac0cffe61327f

def z1117 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0x1ff9ffff00000000 0xfe3ff3fffe000000

def z1118 : W := mkw 0x0008150000000000 0x0000102a00000000 0x1fd81f80fc07c05f 0x3c3fb03f01f80f80

def z1119 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1c181f80fc07f05f 0x3c38303f01f80fe0

def z1120 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff3c00000c 0xfffffffffe780000

def z1121 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000ffffc07f 0x03ffbfc001ffff80

def z1122 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x7de187ecc31e39f3 0xfefbc30fd9863c73

def z1123 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c61870ffe7ce7f 0x5dc78c30e1ffcf9c

def z1124 : W := mkw 0x8000800082100004 0x0100010001042000 0x6ce1866cc31839f3 0xeed9c30cd9863073

def z1125 : W := mkw 0x8000800082100004 0x0100010001042000 0xffdf8000fff8003f 0x03ffbf0001fff000

def z1126 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe010fff80e3f 0x43ffbfc021fff01c

def z1127 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff001809a0 0xfffffffffe003013

def z1128 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe7c6187003ffce7f 0x5fcf8c30e007ff9c

def z1129 : W := mkw 0x180002805405b000 0xc030000500a80b60 0x1fd81800fc07f05f 0x1c3fb03001f80fe0

def z1130 : W := mkw 0x0015400000000000 0x04002a8000000000 0xffdfe000ffe0003f 0x03ffbfc001ffc000

def z1131 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xfebfffff00000000 0xebfd7ffffe000000

def z1132 : W := mkw 0x5080208130891282 0x10a1004102611225 0xf7c6619330993ff5 0xf7ef8cc32661327f

def z1133 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb540619330983fb0 0xf76a80c32661307f

def z1134 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xdfbfffff00000000 0xbbbf7ffffe000000

def z1135 : W := mkw 0x87008224c3366d44 0xa10e010449866cda 0xefe7866cc3ffffff 0xefdfcf0cd987ffff

def z1136 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xf7c6187033e7ce7f 0x5def8c30e067cf9c

def z1137 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f93fc07f05f 0xfc3fb03f27f80fe0

def z1138 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81980fc07f05f 0x103fb03301f80fe0

def z1139 : W := mkw 0xa015c0008a500005 0x05402b800114a000 0xffdf8000ffe0003f 0x01ffbf0001ffc000

def z1140 : W := mkw 0x4080200120880282 0x1081004002411005 0xb540619300983ff1 0xf76a80c32601307f

def z1141 : W := mkw 0x5080208130891282 0x10a1004102611225 0xbdc06193f0993ff7 0xf77b80c327e1327f

def z1142 : W := mkw 0x5080208130891282 0x10a1004102611225 0xf5c061f330993ff5 0xffeb80c3e661327f

def z1143 : W := mkw 0x5080208130891282 0x10a1004102611225 0x9500619330993ff5 0xb32a00c32661327f

def z1144 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff80030 0x03ffbfc001fff000

def z1145 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffffcc00000a 0xffffffffff980000

def z1146 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0xbfd87f93fc1ff9ff 0xff7fb0ff27f83ff3

def z1147 : W := mkw 0x201f5d5a08400019 0x06403ebab4108000 0xffffffff0c600008 0xfffffffffe18c000

def z1148 : W := mkw 0x85008224c3162944 0x810a010449862c52 0xede1867cc31e39f3 0xffdbc30cf9863c73

def z1149 : W := mkw 0x4000200020880002 0x0080004000411000 0xffde6000fff8003f 0x03ffbcc001fff000

def z1150 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00800025 0xfffffffffe010000

def z1151 : W := mkw 0x1e0a1ffa5527fc18 0xe23c143ff4aa4ff8 0x00201fff0007fe40 0xfc00403ffe000ffc

def z1152 : W := mkw 0x5880208134899282 0x50b1004102691325 0xb54061933c99fffd 0xf76a80c3267933ff

def z1153 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb5407993309ffff5 0xff6a80f326613fff

def z1154 : W := mkw 0x0002085000000010 0x02000410a0000000 0xffe7ffff00000000 0xffffcffffe000000

def z1155 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xff1fe000fff8003c 0x03fe3fc001fff000

def z1156 : W := mkw 0x5080208130891282 0x10a1004102611225 0xa140619300993fe5 0xf74280c32601327f

def z1157 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff03000023 0xfffffffffe060000

def z1158 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe7c6187003e7fe7f 0x7dcf8c30e007cffc

def z1159 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xb75e7993001839f1 0xf76ebcf326003073

def z1160 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31ff9ff 0xeed9c30cd9863ff3

def z1161 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe183fff8003f 0xa3ffbfc307fff000

def z1162 : W := mkw 0x190817845405b140 0xc032102f08a80b62 0x1ff81f8cfc07f1df 0xbc3ff03f19f80fe3

def z1163 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffef00000000 0xabffffffde000000

def z1164 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x7ce1e7efc31e39f3 0xeef9c3cfdf863c73

def z1165 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe286187003e7ce6f 0x49c50c30e007cf9c

def z1166 : W := mkw 0x001f5d5a00000018 0x06003ebab4000000 0xffffffff00183190 0xfffffffffe003063

def z1167 : W := mkw 0x1e0a1ff05527fc10 0xe23c143fe0aa4ff8 0x00001fe00007f040 0x3c00003fc0000fe0

def z1168 : W := mkw 0x0015400000000000 0x04002a8000000000 0xffffe7ff00000000 0xffffffcffe000000

def z1169 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x0c21866cc0183990 0xe218430cd9803073

def z1170 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0x62c6186003e7ce6f 0x4cc58c30c007cf9c

def z1171 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0xffdfe000fff8003f 0xe7ffbfc001fff000

def z1172 : W := mkw 0x0602087001224c10 0x220c0410e0024498 0xe3c6187003e7c60e 0x5dc78c30e007cf8c

def z1173 : W := mkw 0x85008224c3162944 0x810a010449862c52 0x6ce1866cc31e31b3 0xaad9c30cd9863c63

def z1174 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1c181f80fc06f010 0x2838303f01f80de0

def z1175 : W := mkw 0xd580a2a5f39f3bc6 0x91ab01454be73e77 0x00000000f31e39f3 0x0000000001e63c73

def z1176 : W := mkw 0x871fdf7ec3366d5c 0xa70e3fbefd866cda 0x4abf9e6cc366c00a 0x08957f3cd986cd80

def z1177 : W := mkw 0x5080208130891282 0x10a1004102611225 0x6ce1866c30993ff5 0xeed9c30cd861327f

def z1178 : W := mkw 0x5080208130891282 0x10a1004102611225 0xb140619330993ff5 0x556280c32661327f

def z1179 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1fd81f80fc07f9df 0xfc3fb03f01f80ff3

def z1180 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1ff81fecfc07f05f 0xfc3ff03fd9f80fe0

def z1181 : W := mkw 0x001d550a00000008 0x04003aaa14000000 0x7c39e7ef00000000 0xe2f873cfde000000

def z1182 : W := mkw 0x180817805405b000 0xc030102f00a80b60 0x1e981f80fc07f05a 0x3c3d303f01f80fe0

def z1183 : W := mkw 0x0000000000000000 0x0000000000000000 0x5fde0000ff60001f 0x00bfbc0001fec000

def z1184 : W := mkw 0xe015e000aad80007 0x05c02bc00155b000 0x5c1fe000ff780010 0x02b83fc001fef000

def z1185 : W := mkw 0x0202085000204410 0x22040410a0004088 0xe3c6181003e7c66f 0x1dc78c302007cf8c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z7,z8,z5,z6]),(0,[z0,z2,z3,z4,z5,z9,z6])],[(0,[z10,z2,z3,z4,z5,z6,z11]),(0,[z12,z2,z3,z4,z13,z5,z6]),(0,[z14,z15,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z16]),(0,[z0,z2,z3,z4,z5,z17,z6])],[(0,[z0,z18,z2,z3,z4,z5,z6]),(0,[z12,z0,z2,z3,z4,z19,z6]),(0,[z0,z2,z20,z3,z4,z5,z6]),(0,[z15,z0,z2,z3,z4,z5,z21]),(1,[z0,z2,z3,z4,z22,z6]),(0,[z23,z0,z2,z3,z4,z24,z6])],[(0,[z0,z2,z3,z4,z25,z5,z6])],[(0,[z26,z0,z2,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z4,z5,z6]),(0,[z0,z28,z2,z4,z5,z29,z6]),(0,[z0,z30,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z31,z4,z5,z6])],[(0,[z0,z2,z3,z4,z32,z5,z6]),(0,[z0,z2,z33,z4,z34,z5,z6])],[(0,[z35,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z33,z36,z4,z5,z6]),(0,[z0,z2,z37,z3,z4,z5,z6]),(0,[z0,z2,z3,z38,z4,z5,z39]),(0,[z0,z2,z3,z4,z40,z5,z6])],[(0,[z2,z3,z36,z4,z5,z6,z11])]],
   [[(0,[z0,z28,z2,z41,z4,z5,z6]),(0,[z0,z42,z2,z3,z4,z43,z6]),(0,[z0,z2,z44,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z45,z5,z6])],[(0,[z0,z2,z3,z4,z5,z46,z6]),(0,[z0,z2,z47,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z48,z6]),(0,[z0,z2,z49,z4,z34,z5,z6]),(0,[z0,z2,z50,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z51,z5,z6]),(1,[z52,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z53,z4,z5,z6]),(0,[z0,z2,z3,z38,z4,z5,z6])],[(0,[z54,z2,z3,z36,z4,z5,z6]),(0,[z55,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z56,z6]),(0,[z0,z2,z3,z4,z57,z5,z6]),(0,[z0,z2,z58,z3,z4,z5,z6])],[(0,[z59,z0,z2,z3,z4,z5,z6])],[(0,[z60,z0,z2,z61,z4,z5,z6]),(0,[z0,z2,z3,z62,z4,z5,z6])],[(0,[z63,z0,z2,z3,z4,z5,z64]),(0,[z0,z2,z3,z4,z65,z5,z6]),(0,[z15,z0,z2,z3,z4,z5,z11]),(0,[z0,z2,z3,z4,z66,z6,z67]),(0,[z68,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z69,z3,z4,z5,z39])],[(0,[z70,z0,z2,z71,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z72,z6]),(0,[z73,z0,z2,z3,z4,z5,z6]),(0,[z74,z0,z2,z3,z4,z5,z6]),(0,[z75,z76,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z77]),(0,[z0,z2,z3,z4,z5,z78,z6])]],
   [[(0,[z0,z79,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z80]),(1,[z0,z81,z3,z4,z5,z6]),(0,[z82,z0,z81,z3,z4,z5,z6])],[(0,[z12,z0,z2,z3,z4,z5,z6]),(0,[z83,z0,z2,z3,z4,z5,z6]),(0,[z84,z0,z2,z3,z4,z5,z6]),(0,[z23,z0,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z34,z5,z6]),(1,[z85,z2,z3,z4,z5,z6]),(0,[z82,z85,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z36,z4,z5,z6]),(0,[z0,z2,z3,z4,z86,z5,z6]),(0,[z0,z87,z2,z3,z4,z5,z6]),(0,[z0,z88,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z89,z6]),(0,[z0,z2,z69,z3,z4,z5,z6])],[(0,[z90,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z91]),(0,[z15,z2,z3,z4,z5,z6,z11]),(0,[z0,z2,z3,z92,z4,z5,z6]),(0,[z93,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z94,z5,z6])],[(0,[z0,z2,z3,z4,z5,z95,z6]),(0,[z15,z0,z2,z3,z4,z5,z6]),(0,[z0,z96,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z97,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z98,z6]),(0,[z99,z0,z2,z3,z4,z100,z6]),(0,[z0,z2,z101,z3,z4,z5,z6]),(0,[z0,z102,z2,z3,z4,z5,z6])],[(0,[z63,z0,z2,z3,z65,z5,z6])],[(0,[z103,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z104,z6]),(0,[z105,z0,z2,z3,z4,z5,z6]),(1,[z0,z106,z3,z4,z19,z6])]],
   [[(0,[z0,z2,z3,z107,z4,z5,z6]),(0,[z60,z0,z2,z3,z108,z5,z6]),(0,[z0,z2,z3,z4,z43,z5,z6])],[(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z110,z6]),(0,[z0,z2,z3,z111,z4,z5,z6]),(0,[z0,z2,z3,z112,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z113,z6]),(0,[z0,z2,z3,z4,z5,z114,z6])],[(0,[z0,z2,z115,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z5,z116]),(0,[z12,z0,z2,z3,z4,z117,z6]),(0,[z118,z0,z2,z3,z4,z5,z6]),(0,[z0,z119,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z120,z5,z6]),(0,[z0,z2,z3,z120,z4,z5,z6])],[(0,[z0,z2,z121,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z122,z6]),(0,[z0,z123,z3,z4,z5,z19,z6]),(0,[z0,z2,z3,z4,z5,z124,z6]),(0,[z0,z2,z3,z53,z41,z4,z5]),(1,[z0,z28,z125,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z126]),(0,[z127,z0,z2,z3,z4,z5,z6]),(0,[z0,z128,z2,z3,z4,z5,z6])],[(0,[z0,z2,z4,z129,z5,z66,z6]),(0,[z0,z2,z3,z4,z5,z130,z6]),(0,[z0,z2,z131,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z132,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z133])],[(1,[z134,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z13,z94,z6]),(0,[z0,z2,z3,z4,z5,z22,z6]),(0,[z0,z2,z3,z4,z5,z6,z135]),(0,[z0,z2,z3,z4,z5,z136,z6])],[(0,[z0,z2,z3,z4,z5,z137,z6]),(0,[z0,z3,z4,z5,z138,z6,z80]),(0,[z0,z2,z3,z139,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z140]),(0,[z0,z2,z3,z4,z141,z5,z6]),(0,[z0,z2,z3,z4,z5,z142,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z143,z6]),(0,[z0,z2,z3,z4,z5,z144,z6])],[(0,[z0,z2,z3,z4,z145,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z146]),(0,[z99,z0,z2,z3,z120,z5,z6])],[(0,[z147,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z148,z6]),(0,[z149,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z137]),(0,[z0,z2,z3,z4,z150,z5,z6]),(0,[z0,z151,z2,z3,z4,z5,z6]),(0,[z23,z0,z2,z3,z8,z5,z6]),(0,[z0,z2,z3,z4,z5,z39,z138])],[],[(0,[z0,z2,z3,z152,z4,z5,z6]),(0,[z0,z153,z2,z3,z4,z5,z6])],[(1,[z60,z2,z3,z4,z117,z6]),(1,[z0,z2,z154,z4,z5,z6]),(0,[z82,z0,z2,z154,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z155,z6]),(0,[z0,z156,z2,z3,z4,z5,z6]),(0,[z0,z157,z2,z3,z4,z5,z6])],[(0,[z158,z99,z0,z2,z4,z5,z6]),(0,[z159,z0,z2,z3,z41,z4,z5]),(0,[z0,z42,z2,z3,z4,z5,z67])]],
   [[],[(0,[z160,z0,z2,z3,z4,z5,z6]),(0,[z161,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z162]),(0,[z0,z2,z3,z4,z163,z5,z6]),(0,[z0,z2,z164,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z6,z67])],[(0,[z166,z0,z2,z3,z4,z5,z6]),(0,[z63,z0,z2,z3,z4,z167,z6]),(0,[z168,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z169,z3,z4,z5,z6]),(1,[z0,z2,z170,z4,z5,z6])],[(0,[z171,z0,z2,z3,z4,z5,z6]),(0,[z0,z172,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z173,z5,z6]),(1,[z0,z2,z3,z4,z174,z67])],[(0,[z0,z2,z3,z175,z4,z5,z6]),(0,[z176,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z177,z5,z6]),(0,[z0,z2,z69,z3,z7,z5,z6])],[(0,[z0,z2,z178,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z179,z6])],[(0,[z0,z2,z3,z180,z4,z5,z6]),(0,[z181,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z182,z5,z6]),(0,[z0,z2,z3,z4,z5,z183,z6]),(0,[z184,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z185,z3,z4,z5,z6])],[(0,[z0,z123,z2,z3,z4,z5,z6]),(0,[z0,z2,z186,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z187]),(0,[z0,z2,z3,z188,z4,z5,z6]),(0,[z0,z2,z3,z189,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z190,z4,z5,z6]),(0,[z0,z191,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z132,z6]),(0,[z0,z2,z3,z4,z5,z192,z6])],[(0,[z0,z2,z3,z193,z4,z5,z6]),(0,[z0,z2,z3,z65,z5,z78,z6]),(1,[z0,z2,z3,z4,z51,z6]),(0,[z0,z2,z3,z4,z194,z5,z6]),(0,[z0,z2,z195,z3,z4,z5,z6]),(1,[z0,z2,z33,z4,z129,z6]),(0,[z0,z2,z81,z3,z4,z5,z6]),(0,[z0,z2,z69,z3,z38,z5,z6])],[(0,[z134,z0,z2,z3,z4,z65,z6]),(0,[z0,z2,z196,z3,z4,z5,z6]),(0,[z0,z197,z106,z3,z4,z5,z6]),(0,[z198,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z7,z4,z5,z199]),(0,[z0,z2,z3,z200,z4,z5,z6])],[(0,[z0,z2,z3,z4,z108,z5,z6]),(0,[z201,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z138,z202])],[(1,[z0,z203,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z204,z6]),(0,[z0,z2,z3,z205,z4,z5,z6])],[(1,[z0,z2,z3,z4,z206,z6]),(0,[z0,z207,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z49,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z209,z6]),(0,[z210,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z211]),(0,[z212,z0,z2,z3,z4,z5,z6]),(0,[z0,z106,z2,z3,z4,z43,z6]),(0,[z0,z2,z3,z4,z213,z5,z6]),(0,[z184,z2,z3,z4,z5,z78,z6])],[(0,[z0,z2,z214,z3,z4,z5,z6]),(0,[z0,z2,z215,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z216]),(0,[z0,z2,z3,z4,z5,z6,z217])]],
   [[(0,[z218,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z219,z6]),(0,[z0,z2,z220,z3,z4,z5,z6]),(0,[z0,z2,z3,z221,z4,z5,z6])],[(0,[z0,z125,z3,z41,z4,z5,z6]),(0,[z0,z2,z3,z4,z222,z5,z6]),(0,[z23,z0,z3,z4,z8,z5,z6]),(0,[z0,z197,z2,z3,z4,z19,z6]),(1,[z198,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z7,z4,z5,z223])],[(0,[z10,z0,z121,z3,z4,z5,z6]),(0,[z224,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z225,z5,z6]),(0,[z0,z2,z3,z4,z13,z5,z6]),(0,[z0,z226,z2,z3,z4,z5,z80])],[(0,[z70,z2,z121,z3,z4,z5,z6]),(0,[z0,z227,z2,z3,z4,z5,z6]),(0,[z60,z12,z2,z3,z4,z5,z6]),(0,[z0,z2,z228,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z5,z11]),(0,[z0,z2,z3,z4,z5,z229,z6]),(0,[z75,z0,z2,z3,z4,z132,z6]),(0,[z0,z2,z33,z3,z4,z129,z6]),(0,[z0,z2,z3,z4,z5,z230,z6])],[(0,[z231,z0,z2,z3,z4,z5,z6]),(0,[z70,z10,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z232]),(0,[z233,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z234,z5,z6]),(0,[z0,z2,z3,z4,z5,z235,z6]),(0,[z75,z0,z3,z4,z5,z6,z80]),(0,[z236,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z237,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z238,z6]),(0,[z0,z239,z2,z3,z4,z5,z6]),(0,[z0,z2,z240,z125,z4,z5,z6]),(1,[z0,z241,z3,z4,z5,z6]),(1,[z0,z242,z3,z4,z5,z6]),(0,[z82,z0,z242,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z243])],[(0,[z158,z0,z2,z41,z4,z5,z6]),(0,[z244,z0,z2,z3,z4,z5,z6]),(0,[z23,z0,z2,z3,z4,z5,z72]),(0,[z245,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z246,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z247,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z248]),(0,[z0,z249,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z100,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z250]),(0,[z0,z251,z2,z3,z4,z5,z6])],[(0,[z252,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z253,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z254]),(0,[z0,z2,z3,z4,z5,z6,z255])],[(0,[z54,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z43,z6,z67])],[(0,[z0,z2,z3,z4,z256,z5,z6]),(0,[z23,z0,z2,z257,z4,z5,z6])],[(0,[z0,z121,z3,z4,z8,z5,z6]),(1,[z0,z2,z188,z4,z5,z6]),(0,[z99,z0,z241,z3,z4,z5,z6])],[(0,[z258,z0,z2,z3,z65,z5,z6]),(0,[z0,z2,z3,z4,z5,z259,z6]),(0,[z158,z0,z2,z3,z260,z5,z6]),(0,[z0,z2,z208,z3,z4,z5,z6])],[(0,[z14,z70,z2,z3,z4,z5,z6]),(0,[z0,z2,z261,z3,z4,z5,z6]),(0,[z0,z2,z41,z4,z5,z6,z262])]],
   [[(0,[z0,z2,z3,z263,z4,z5,z6]),(0,[z0,z2,z3,z264,z4,z5,z6]),(0,[z0,z197,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z265,z6])],[(0,[z258,z2,z3,z4,z5,z117,z6]),(0,[z0,z2,z3,z4,z5,z6,z266]),(0,[z0,z2,z3,z4,z5,z6,z11]),(0,[z0,z2,z3,z8,z34,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z63,z258,z2,z3,z4,z5,z6]),(1,[z0,z1,z3,z267,z5,z6])],[(0,[z10,z258,z2,z3,z4,z5,z6]),(0,[z12,z0,z2,z3,z4,z13,z6]),(0,[z158,z0,z3,z41,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z138,z262]),(0,[z0,z2,z3,z4,z268,z5,z6]),(0,[z0,z42,z2,z3,z4,z129,z6])],[(0,[z0,z2,z3,z4,z5,z6,z269]),(0,[z0,z2,z3,z4,z5,z270,z6]),(0,[z0,z2,z3,z4,z5,z271,z6]),(1,[z70,z2,z71,z4,z5,z6]),(0,[z99,z0,z226,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z272,z6])],[(0,[z0,z2,z273,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z51,z65,z6]),(0,[z0,z2,z3,z107,z274,z5,z6]),(1,[z0,z2,z3,z53,z4,z5]),(0,[z0,z2,z69,z3,z8,z5,z6]),(0,[z0,z275,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z276,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z277]),(0,[z278,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z135]),(0,[z0,z226,z2,z3,z4,z5,z138])],[(0,[z0,z2,z279,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z280]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z4,z281,z5,z6]),(0,[z0,z226,z2,z240,z3,z4,z5]),(0,[z0,z2,z3,z282,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z283]),(0,[z0,z2,z3,z284,z4,z5,z6]),(1,[z0,z2,z3,z4,z100,z6]),(0,[z285,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z206,z6]),(1,[z0,z2,z3,z4,z286,z6]),(0,[z0,z2,z3,z4,z287,z5,z6]),(0,[z0,z2,z3,z4,z129,z19,z6]),(0,[z0,z2,z3,z4,z5,z39,z80])],[(0,[z288,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z289,z4,z5,z6]),(0,[z0,z2,z290,z3,z4,z5,z6]),(0,[z0,z2,z3,z274,z4,z5,z6])],[(0,[z291,z0,z2,z3,z4,z5,z6]),(0,[z63,z0,z2,z3,z107,z5,z6]),(0,[z292,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z293,z4,z5,z6]),(0,[z0,z2,z3,z294,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z5,z202])],[(0,[z0,z2,z3,z4,z295,z5,z6]),(0,[z158,z0,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z296,z5,z6])],[(0,[z0,z2,z3,z4,z5,z297,z6]),(0,[z0,z2,z3,z298,z4,z5,z6]),(0,[z0,z2,z203,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z299,z6])],[(0,[z0,z2,z300,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z204,z5,z6]),(0,[z23,z0,z2,z3,z4,z301,z6]),(0,[z0,z2,z3,z4,z19,z66,z6]),(0,[z0,z2,z4,z5,z6,z302,z80]),(0,[z0,z2,z208,z4,z5,z29,z6]),(0,[z0,z2,z3,z4,z5,z6,z303])],[(0,[z0,z304,z2,z3,z4,z5,z6]),(0,[z0,z2,z71,z33,z4,z5,z6]),(1,[z0,z2,z3,z180,z5,z6]),(0,[z0,z2,z3,z4,z5,z305,z6])]],
   [[(0,[z0,z2,z306,z3,z4,z5,z6]),(0,[z0,z2,z307,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z308,z5,z6]),(0,[z0,z2,z3,z4,z5,z21,z6]),(0,[z0,z309,z2,z3,z4,z5,z6])],[(0,[z0,z123,z1,z3,z4,z5,z6]),(0,[z0,z2,z71,z4,z5,z66,z6]),(0,[z159,z0,z2,z3,z4,z5,z6]),(0,[z310,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z311,z5,z6]),(0,[z0,z2,z3,z94,z5,z78,z6])],[(0,[z0,z312,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z41,z4,z5,z6]),(0,[z313,z0,z2,z3,z4,z5,z6]),(0,[z314,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z315,z5,z6]),(0,[z316,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z317,z5,z6]),(0,[z158,z0,z2,z3,z97,z5,z6]),(0,[z0,z2,z318,z3,z4,z5,z6]),(0,[z319,z0,z2,z3,z4,z5,z6])],[(0,[z63,z0,z2,z279,z4,z5,z6]),(0,[z0,z2,z3,z4,z320,z5,z6])],[(0,[z321,z0,z2,z3,z4,z5,z6]),(1,[z258,z2,z3,z107,z5,z6]),(0,[z0,z2,z3,z4,z322,z5,z6]),(0,[z0,z2,z3,z4,z323,z5,z6]),(0,[z0,z324,z2,z3,z4,z5,z6]),(1,[z0,z226,z3,z4,z5,z138]),(0,[z0,z2,z208,z33,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z325,z6])],[(0,[z0,z326,z2,z3,z4,z5,z6]),(0,[z0,z327,z2,z3,z4,z5,z6]),(0,[z75,z0,z2,z293,z4,z5,z6]),(0,[z328,z0,z2,z4,z5,z6,z80])],[(0,[z0,z226,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z329,z6]),(0,[z75,z0,z2,z3,z4,z5,z138]),(0,[z0,z2,z208,z4,z5,z66,z6]),(0,[z0,z2,z3,z4,z330,z5,z6]),(0,[z331,z0,z2,z3,z4,z129,z6]),(0,[z0,z2,z3,z332,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z333]),(0,[z0,z2,z3,z38,z4,z5,z202])]],
   [[(0,[z0,z2,z208,z3,z7,z5,z6]),(0,[z0,z2,z3,z334,z4,z5,z6])],[(0,[z0,z2,z49,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z335,z6])],[(0,[z0,z2,z3,z4,z336,z5,z6]),(0,[z0,z2,z3,z4,z337,z5,z6]),(0,[z2,z3,z4,z5,z21,z6,z11]),(0,[z158,z239,z2,z3,z4,z5,z6]),(0,[z338,z0,z2,z3,z4,z5,z6]),(0,[z339,z0,z2,z3,z4,z5,z6]),(1,[z0,z340,z3,z4,z5,z6])],[(0,[z12,z0,z2,z3,z274,z4,z6]),(0,[z0,z2,z3,z4,z5,z341,z6]),(0,[z0,z2,z3,z342,z4,z5,z6]),(0,[z0,z2,z3,z4,z343,z5,z6]),(0,[z82,z0,z2,z3,z4,z94,z6])],[(0,[z0,z28,z3,z4,z5,z6,z80]),(0,[z344,z0,z2,z3,z4,z5,z6]),(0,[z0,z345,z2,z3,z4,z5,z6])],[(0,[z0,z346,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z347,z5,z6]),(0,[z0,z2,z348,z3,z4,z5,z6])],[(0,[z0,z2,z3,z274,z65,z5,z6]),(0,[z0,z2,z349,z3,z4,z5,z6]),(1,[z0,z2,z350,z4,z5,z6])],[(0,[z0,z2,z3,z351,z4,z5,z6]),(0,[z352,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z34,z5,z66,z6]),(0,[z0,z2,z3,z4,z5,z6,z353]),(0,[z0,z2,z69,z3,z4,z5,z202]),(0,[z354,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z355,z4,z5,z6]),(0,[z0,z2,z356,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z357,z6]),(0,[z0,z2,z358,z3,z4,z5,z6])],[(0,[z359,z0,z121,z3,z4,z5,z6]),(0,[z12,z0,z2,z3,z4,z43,z6]),(0,[z360,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z361,z5,z6]),(0,[z0,z2,z3,z362,z4,z5,z6]),(0,[z99,z0,z340,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z363,z5,z6])],[(0,[z70,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z364,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z238]),(0,[z60,z2,z3,z107,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z365,z6]),(0,[z0,z2,z69,z31,z4,z5,z6])],[(0,[z14,z10,z2,z3,z4,z5,z6]),(1,[z366,z2,z3,z4,z5,z6]),(0,[z0,z2,z293,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z367,z5,z6]),(0,[z0,z2,z3,z4,z368,z5,z6]),(0,[z0,z2,z3,z274,z94,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z369]),(0,[z2,z3,z4,z65,z5,z117,z6]),(0,[z0,z2,z3,z370,z4,z5,z6]),(1,[z0,z2,z3,z97,z5,z6]),(0,[z371,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z69,z3,z34,z5,z6])],[(0,[z60,z2,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z286,z6]),(0,[z0,z2,z3,z372,z4,z5,z6])],[(0,[z60,z10,z2,z3,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z373,z3,z4,z5,z6]),(0,[z0,z2,z374,z3,z4,z5,z6])],[(1,[z313,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z375,z6]),(0,[z0,z2,z3,z4,z5,z67,z202])]],
   [[(0,[z0,z2,z376,z3,z4,z5,z6]),(0,[z0,z2,z377,z3,z4,z5,z6]),(0,[z0,z2,z3,z107,z5,z78,z6]),(0,[z0,z2,z3,z4,z117,z78,z6]),(0,[z0,z2,z3,z4,z5,z378,z6]),(0,[z0,z2,z3,z4,z5,z379,z6])],[(0,[z380,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z13,z5,z117,z6]),(0,[z0,z2,z3,z4,z381,z5,z6]),(0,[z0,z2,z3,z4,z5,z382,z6]),(0,[z0,z2,z3,z383,z4,z5,z6])],[(0,[z0,z197,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z384,z6]),(0,[z0,z385,z2,z3,z4,z5,z6])],[(0,[z63,z0,z203,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z167,z5,z6]),(0,[z0,z2,z3,z4,z5,z386,z6]),(1,[z239,z2,z3,z4,z5,z6]),(0,[z387,z0,z2,z3,z4,z5,z6]),(0,[z388,z0,z2,z3,z4,z5,z6]),(0,[z198,z197,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z389,z5,z6]),(0,[z60,z0,z2,z3,z180,z5,z6]),(0,[z0,z390,z2,z3,z4,z5,z6]),(0,[z0,z391,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z174,z5,z6])],[],[(0,[z0,z2,z3,z392,z4,z5,z6]),(0,[z0,z3,z4,z43,z5,z19,z6]),(0,[z99,z313,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z393,z5,z6]),(0,[z0,z2,z394,z3,z4,z5,z6]),(0,[z0,z2,z3,z395,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z396,z6])]],
   [[(1,[z0,z2,z397,z4,z5,z6]),(0,[z0,z2,z3,z398,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z266]),(0,[z0,z226,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z399,z5,z6]),(0,[z99,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z400,z6]),(0,[z0,z42,z2,z3,z4,z165,z6])],[(0,[z0,z3,z4,z8,z5,z19,z6]),(0,[z0,z401,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z402,z6])],[(0,[z403,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z121,z3,z4,z5,z6]),(0,[z404,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z405,z5,z6]),(0,[z0,z2,z49,z3,z7,z5,z6]),(0,[z0,z2,z240,z3,z4,z5,z29])],[(0,[z0,z2,z406,z3,z4,z5,z6]),(0,[z63,z0,z407,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z11,z202])],[(0,[z0,z2,z3,z4,z5,z29,z80]),(0,[z0,z2,z3,z4,z5,z6,z408]),(0,[z0,z2,z409,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z39,z21]),(0,[z158,z0,z2,z4,z5,z29,z6]),(0,[z0,z2,z3,z267,z5,z6,z202]),(0,[z0,z2,z410,z3,z4,z5,z6]),(0,[z0,z2,z411,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z412,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z4,z34,z5,z6]),(0,[z82,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z413,z6])],[(0,[z0,z123,z3,z4,z8,z5,z6]),(0,[z414,z0,z2,z3,z4,z5,z6])],[(0,[z63,z2,z3,z4,z65,z5,z6]),(0,[z0,z2,z3,z4,z5,z66,z6]),(0,[z99,z0,z2,z3,z4,z5,z39])],[(0,[z415,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z71,z3,z4,z5,z6]),(0,[z0,z2,z340,z3,z4,z5,z6])],[(0,[z416,z0,z2,z3,z4,z5,z6]),(0,[z258,z0,z2,z3,z107,z5,z6]),(0,[z0,z2,z3,z4,z417,z5,z6]),(0,[z99,z0,z28,z2,z4,z5,z6]),(0,[z418,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z240,z3,z4,z5,z39]),(0,[z0,z419,z2,z3,z4,z5,z6])],[(1,[z0,z2,z49,z34,z5,z6]),(0,[z420,z0,z2,z3,z4,z5,z6]),(0,[z0,z421,z2,z3,z4,z5,z6])],[(0,[z0,z422,z2,z3,z4,z5,z6]),(1,[z63,z2,z3,z65,z5,z6]),(0,[z0,z2,z3,z423,z4,z5,z6]),(0,[z99,z0,z2,z3,z4,z5,z6])],[(0,[z10,z2,z3,z36,z4,z5,z6]),(0,[z424,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z425,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z426]),(0,[z427,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z33,z3,z4,z66,z6])]],
   [[(0,[z0,z2,z3,z428,z4,z5,z6]),(1,[z168,z2,z3,z4,z5,z6]),(0,[z23,z0,z2,z3,z267,z5,z6]),(0,[z0,z2,z240,z3,z4,z5,z6])],[(0,[z429,z0,z2,z3,z4,z5,z6]),(0,[z430,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z431,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z80,z202])],[(0,[z0,z2,z3,z432,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z39,z11]),(0,[z433,z0,z2,z3,z4,z5,z6]),(0,[z0,z241,z2,z3,z4,z5,z6]),(0,[z0,z2,z434,z3,z4,z5,z6])],[(1,[z0,z197,z3,z4,z43,z6]),(0,[z0,z2,z3,z4,z129,z6,z67])],[(0,[z0,z2,z3,z4,z5,z116,z6]),(0,[z82,z60,z0,z2,z3,z4,z6]),(0,[z0,z435,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z436,z5,z6]),(0,[z0,z2,z3,z4,z5,z19,z6]),(0,[z0,z2,z3,z4,z43,z78,z6]),(0,[z0,z76,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z437,z4,z5,z6]),(0,[z0,z2,z438,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z439])],[(0,[z60,z0,z2,z3,z4,z19,z6]),(0,[z0,z2,z3,z4,z5,z6,z440])],[(0,[z441,z0,z2,z3,z4,z5,z6]),(0,[z258,z12,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z442,z6]),(0,[z82,z12,z0,z2,z3,z4,z6]),(0,[z75,z0,z2,z3,z4,z5,z80])],[(0,[z0,z2,z3,z4,z5,z6,z443]),(0,[z60,z63,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z444,z6])]],
   [[(0,[z63,z0,z2,z3,z4,z286,z6]),(0,[z0,z2,z3,z4,z445,z5,z6]),(0,[z0,z2,z446,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z39,z6])],[(0,[z0,z2,z3,z4,z5,z6,z447]),(0,[z0,z2,z3,z267,z4,z5,z6]),(0,[z0,z2,z3,z4,z448,z5,z6]),(0,[z0,z2,z170,z69,z4,z5,z6])],[(0,[z0,z2,z125,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z449,z5,z6]),(1,[z331,z0,z2,z4,z66,z6])],[(0,[z450,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z350,z4,z5,z6]),(0,[z0,z2,z451,z3,z4,z5,z6]),(0,[z452,z0,z2,z3,z4,z5,z6]),(0,[z0,z453,z2,z3,z4,z5,z6])],[(0,[z2,z121,z3,z4,z65,z5,z6]),(0,[z0,z454,z2,z3,z4,z5,z6]),(0,[z99,z0,z2,z208,z4,z5,z6])],[(1,[z0,z455,z3,z4,z5,z6])],[(0,[z456,z0,z2,z3,z4,z5,z6]),(0,[z457,z0,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z5,z266]),(0,[z0,z458,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z459]),(0,[z0,z2,z3,z4,z460,z5,z6]),(0,[z99,z0,z2,z4,z5,z6,z262])],[(0,[z359,z0,z123,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z461,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z462]),(0,[z0,z42,z2,z3,z4,z66,z6]),(0,[z0,z2,z33,z4,z129,z5,z6]),(1,[z414,z2,z3,z4,z5,z6]),(0,[z82,z414,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z39,z6,z202])]],
   [[(0,[z2,z121,z3,z36,z4,z5,z6]),(0,[z0,z2,z3,z463,z4,z5,z6]),(0,[z0,z2,z464,z3,z4,z5,z6]),(0,[z0,z2,z240,z4,z5,z29,z6]),(1,[z0,z2,z3,z274,z94,z6])],[(0,[z0,z226,z3,z41,z4,z5,z6])],[(1,[z0,z2,z3,z260,z5,z6]),(1,[z0,z2,z3,z4,z24,z6]),(0,[z0,z197,z3,z4,z8,z5,z6]),(0,[z0,z2,z3,z4,z19,z6,z67]),(1,[z465,z2,z3,z4,z5,z6]),(0,[z0,z2,z466,z3,z4,z5,z6]),(0,[z331,z0,z2,z4,z5,z66,z6])],[(0,[z0,z2,z3,z4,z467,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6])],[(0,[z60,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z41,z4,z34,z5,z6]),(0,[z0,z2,z240,z41,z4,z5,z6]),(0,[z0,z2,z3,z468,z4,z5,z6]),(0,[z469,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z470,z3,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z5,z471]),(0,[z0,z2,z3,z472,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z473,z6]),(0,[z474,z0,z2,z3,z4,z5,z6]),(1,[z15,z2,z3,z4,z5,z11]),(0,[z0,z2,z3,z4,z5,z11,z67]),(0,[z0,z2,z3,z475,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z64]),(0,[z0,z476,z2,z3,z4,z5,z6]),(0,[z0,z2,z477,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z174,z6,z67])]],
   [[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z478,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z479]),(0,[z0,z2,z257,z3,z4,z5,z6]),(0,[z0,z2,z3,z480,z4,z5,z6]),(0,[z0,z197,z2,z3,z4,z43,z6]),(0,[z0,z2,z208,z3,z34,z5,z6]),(0,[z0,z2,z3,z481,z4,z5,z6]),(0,[z0,z2,z33,z3,z4,z5,z6]),(0,[z0,z2,z3,z482,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z483,z6]),(0,[z0,z2,z3,z484,z4,z5,z6]),(0,[z485,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z267,z5,z6]),(0,[z0,z42,z2,z3,z4,z19,z6]),(1,[z0,z2,z3,z4,z486,z6]),(0,[z0,z2,z3,z4,z5,z80,z262]),(0,[z0,z2,z4,z34,z5,z29,z6]),(0,[z487,z0,z2,z3,z4,z5,z6]),(0,[z0,z488,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z489,z6]),(0,[z0,z2,z3,z4,z5,z490,z6])],[(0,[z0,z2,z125,z4,z5,z6,z262]),(0,[z0,z491,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z7,z4,z5,z6]),(0,[z492,z0,z2,z3,z4,z5,z6])],[(0,[z70,z2,z71,z3,z4,z5,z6]),(0,[z0,z2,z493,z3,z4,z5,z6]),(0,[z75,z0,z2,z240,z3,z4,z5]),(0,[z0,z2,z3,z4,z129,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z494])],[(0,[z14,z2,z3,z36,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z117,z6]),(0,[z0,z2,z3,z4,z5,z495,z6]),(0,[z0,z2,z3,z4,z5,z6,z202])],[(0,[z0,z2,z3,z397,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z117,z6]),(0,[z0,z2,z3,z4,z496,z5,z6]),(0,[z0,z2,z3,z497,z4,z5,z6])],[(0,[z498,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z499,z5,z6]),(0,[z0,z2,z3,z500,z4,z5,z6]),(0,[z0,z2,z3,z4,z501,z5,z6])],[(1,[z359,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z502]),(1,[z0,z2,z4,z5,z6,z302]),(1,[z0,z2,z208,z7,z5,z6]),(1,[z385,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z167,z6]),(1,[z158,z0,z41,z4,z5,z6]),(0,[z0,z503,z2,z3,z4,z5,z6]),(0,[z0,z2,z69,z3,z5,z39,z6]),(0,[z504,z0,z2,z3,z4,z5,z6])],[(0,[z54,z0,z2,z36,z4,z5,z6]),(0,[z0,z407,z2,z3,z4,z5,z6]),(0,[z63,z0,z2,z3,z4,z5,z238]),(0,[z0,z1,z3,z4,z5,z19,z6]),(0,[z0,z2,z3,z7,z267,z5,z6]),(0,[z505,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z506,z6]),(0,[z0,z28,z2,z125,z4,z5,z6])],[(0,[z10,z0,z123,z3,z4,z5,z6]),(0,[z331,z0,z2,z3,z4,z66,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z208,z36,z4,z5,z6]),(0,[z70,z2,z3,z4,z5,z6,z11]),(0,[z0,z2,z3,z507,z4,z5,z6]),(0,[z0,z508,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z509,z6]),(1,[z2,z3,z4,z5,z396,z6])],[(0,[z14,z2,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z21,z202]),(0,[z23,z0,z2,z188,z4,z5,z6]),(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z396,z78,z6]),(0,[z0,z2,z3,z4,z165,z174,z5])],[(0,[z54,z70,z2,z3,z4,z5,z6]),(0,[z63,z2,z3,z4,z13,z5,z6]),(0,[z0,z2,z3,z4,z13,z78,z6]),(0,[z99,z385,z2,z3,z4,z5,z6])],[(0,[z10,z2,z3,z4,z13,z5,z6]),(0,[z0,z2,z511,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z512,z5,z6]),(0,[z0,z2,z3,z4,z5,z513,z6]),(0,[z0,z2,z3,z4,z5,z6,z514])]],
   [[(1,[z0,z2,z3,z4,z5,z223]),(1,[z0,z2,z3,z173,z5,z6]),(0,[z0,z42,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z177,z5,z6]),(0,[z0,z2,z3,z515,z4,z5,z6])],[(0,[z0,z2,z3,z4,z516,z5,z6]),(0,[z60,z0,z455,z3,z4,z5,z6]),(0,[z0,z2,z517,z3,z4,z5,z6]),(0,[z0,z2,z3,z7,z5,z6,z202])],[(0,[z518,z0,z2,z3,z4,z5,z6]),(0,[z519,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z69,z3,z267,z5,z6]),(0,[z0,z2,z3,z4,z43,z129,z6]),(0,[z0,z2,z520,z3,z4,z5,z6])],[(0,[z0,z2,z521,z3,z4,z5,z6]),(0,[z522,z0,z2,z3,z4,z5,z6]),(0,[z75,z0,z2,z350,z4,z5,z6]),(0,[z523,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z524,z6]),(0,[z525,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z526,z6]),(0,[z0,z2,z3,z527,z4,z5,z6]),(0,[z0,z528,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z529,z5,z6])],[(0,[z530,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z531,z4,z5,z6]),(0,[z158,z52,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z24,z6]),(0,[z23,z0,z2,z3,z4,z5,z135])],[(0,[z0,z2,z3,z532,z4,z5,z6]),(0,[z328,z0,z2,z3,z4,z5,z6]),(0,[z0,z226,z3,z4,z5,z138,z6]),(0,[z99,z0,z2,z240,z4,z5,z6]),(0,[z99,z0,z2,z3,z173,z5,z6])]],
   [[(0,[z0,z455,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z108,z5,z6]),(0,[z0,z2,z3,z533,z4,z5,z6]),(0,[z534,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z535,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z43,z94,z6]),(0,[z536,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z36,z4,z34,z5,z6]),(1,[z0,z2,z3,z4,z5,z116]),(0,[z0,z537,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z538,z4,z5,z6]),(0,[z0,z2,z3,z539,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z540])],[(0,[z0,z541,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z542]),(0,[z0,z2,z49,z3,z34,z5,z6]),(0,[z543,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z544,z5,z6])],[(1,[z0,z2,z545,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z199]),(0,[z0,z2,z3,z4,z5,z29,z6]),(0,[z0,z2,z3,z4,z5,z6,z262]),(1,[z0,z2,z3,z4,z5,z375]),(0,[z82,z0,z2,z3,z4,z5,z375])],[(0,[z0,z2,z3,z546,z4,z5,z6]),(0,[z2,z3,z107,z4,z65,z5,z6]),(0,[z258,z2,z3,z107,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z486,z6])],[(0,[z547,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z548,z5,z6]),(0,[z63,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z549,z5,z6]),(0,[z0,z550,z2,z3,z4,z5,z6])],[(0,[z10,z0,z2,z3,z4,z5,z6]),(0,[z359,z2,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z551,z5,z6]),(0,[z552,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z359,z10,z2,z3,z4,z5,z6]),(0,[z258,z2,z121,z3,z4,z5,z6]),(0,[z2,z121,z3,z4,z13,z5,z6]),(0,[z0,z2,z3,z41,z4,z5,z6]),(0,[z0,z3,z41,z4,z5,z6,z80]),(0,[z0,z553,z2,z3,z4,z5,z6]),(0,[z0,z2,z554,z3,z4,z5,z6]),(0,[z0,z197,z3,z4,z43,z5,z6]),(0,[z0,z2,z3,z4,z555,z5,z6]),(0,[z0,z2,z556,z3,z4,z5,z6]),(0,[z0,z2,z557,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z471]),(0,[z0,z2,z3,z4,z94,z19,z6]),(1,[z76,z2,z3,z4,z5,z6]),(0,[z558,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z559,z4,z5,z6]),(0,[z0,z2,z560,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z561,z6]),(0,[z562,z0,z2,z3,z4,z5,z6])],[(0,[z123,z2,z121,z3,z4,z5,z6]),(0,[z0,z197,z121,z3,z4,z5,z6]),(1,[z23,z0,z3,z8,z5,z6]),(0,[z0,z2,z3,z4,z563,z5,z6]),(0,[z564,z0,z2,z3,z4,z5,z6])],[(0,[z565,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z566]),(0,[z0,z2,z567,z3,z4,z5,z6]),(0,[z331,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z568]),(0,[z82,z0,z2,z3,z4,z5,z568]),(0,[z0,z2,z3,z4,z5,z39,z67])],[(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z570,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z571,z5,z6]),(0,[z0,z2,z3,z7,z4,z5,z6])],[(0,[z10,z2,z3,z4,z65,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z572]),(0,[z0,z573,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z221,z5,z6]),(0,[z0,z2,z3,z4,z5,z574,z6]),(0,[z0,z2,z3,z274,z4,z78,z6]),(0,[z0,z2,z3,z4,z5,z6,z575]),(0,[z0,z2,z3,z4,z5,z6,z67])],[(0,[z576,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z577,z6])]],
   [[],[(0,[z0,z2,z3,z578,z4,z5,z6]),(0,[z0,z2,z579,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z580]),(0,[z0,z581,z2,z3,z4,z5,z6])],[(0,[z14,z0,z2,z3,z4,z5,z21]),(0,[z0,z106,z3,z4,z5,z19,z6]),(0,[z0,z582,z2,z3,z4,z5,z6])],[(0,[z0,z123,z2,z3,z4,z122,z6]),(0,[z0,z2,z3,z4,z583,z5,z6]),(0,[z0,z2,z584,z3,z4,z5,z6]),(0,[z0,z2,z3,z585,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z586,z6]),(0,[z0,z2,z3,z4,z5,z6,z587]),(0,[z0,z2,z3,z588,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z589]),(0,[z590,z0,z2,z3,z4,z5,z6]),(0,[z0,z591,z2,z3,z4,z5,z6])],[(0,[z75,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z592,z4,z5,z6]),(0,[z82,z0,z2,z592,z4,z5,z6])],[(0,[z593,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z594,z3,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z5,z137]),(0,[z0,z2,z595,z3,z4,z5,z6]),(1,[z328,z0,z2,z4,z5,z6]),(0,[z0,z596,z2,z3,z4,z5,z6])],[(0,[z2,z121,z3,z4,z5,z6,z11]),(0,[z0,z2,z597,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z64]),(1,[z0,z598,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z599,z6]),(0,[z0,z2,z3,z4,z5,z21,z67]),(0,[z0,z106,z2,z3,z4,z19,z6])]],
   [[(0,[z70,z0,z2,z36,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z600,z6]),(0,[z0,z2,z601,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z602,z6]),(1,[z75,z0,z3,z4,z5,z80]),(1,[z0,z42,z2,z3,z4,z165])],[(0,[z75,z0,z2,z3,z221,z5,z6]),(0,[z0,z2,z3,z4,z5,z138,z29])],[(0,[z0,z2,z3,z4,z260,z5,z6]),(0,[z0,z3,z267,z4,z8,z5,z6]),(0,[z0,z2,z3,z4,z603,z5,z6]),(0,[z0,z604,z2,z3,z4,z5,z6])],[(0,[z23,z366,z2,z3,z4,z5,z6]),(0,[z99,z75,z0,z2,z3,z4,z5]),(0,[z0,z2,z605,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z606])],[(0,[z0,z2,z3,z4,z5,z6,z302]),(0,[z0,z2,z3,z4,z5,z6,z607]),(0,[z0,z242,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z608,z5,z6])],[(0,[z0,z2,z3,z4,z122,z5,z6]),(0,[z2,z71,z3,z36,z4,z5,z6]),(0,[z12,z2,z3,z4,z65,z5,z6]),(0,[z0,z2,z3,z609,z4,z5,z6]),(0,[z0,z2,z3,z4,z610,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z611])],[(0,[z0,z2,z3,z4,z5,z612,z6]),(0,[z60,z0,z2,z3,z4,z13,z6]),(0,[z14,z0,z2,z3,z4,z5,z11]),(0,[z75,z0,z226,z3,z4,z5,z6]),(0,[z0,z2,z613,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z614])],[(0,[z615,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z616,z5,z6]),(1,[z0,z2,z3,z4,z5,z72]),(0,[z0,z2,z3,z4,z617,z5,z6]),(0,[z618,z0,z2,z3,z4,z5,z6]),(0,[z619,z0,z2,z3,z4,z5,z6]),(0,[z197,z573,z2,z3,z4,z5,z6]),(0,[z620,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z568]),(0,[z82,z0,z2,z3,z5,z78,z6]),(1,[z0,z2,z31,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z621,z6])]],
   [[(0,[z60,z0,z2,z397,z4,z5,z6])],[(0,[z0,z2,z622,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z94,z117,z6]),(0,[z0,z2,z3,z623,z4,z5,z6]),(0,[z0,z2,z3,z4,z624,z5,z6])],[(0,[z0,z2,z3,z4,z5,z625,z6]),(1,[z0,z2,z279,z4,z5,z6]),(0,[z0,z2,z3,z626,z4,z5,z6]),(0,[z0,z2,z3,z4,z627,z5,z6]),(0,[z628,z0,z2,z3,z4,z5,z6])],[(0,[z629,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z630,z4,z5,z6]),(0,[z331,z0,z2,z33,z4,z5,z6]),(0,[z99,z0,z2,z3,z4,z5,z202])],[(0,[z0,z2,z631,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z632,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z633]),(0,[z14,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z257,z4,z5,z6]),(0,[z0,z2,z3,z4,z301,z5,z6]),(0,[z0,z2,z3,z8,z5,z6,z202]),(0,[z0,z85,z2,z3,z4,z5,z6])],[(0,[z634,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z240,z3,z4,z5,z202])],[(0,[z0,z106,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z138,z6]),(0,[z0,z2,z3,z4,z5,z6,z635]),(0,[z0,z2,z154,z3,z4,z5,z6])],[(0,[z0,z121,z3,z4,z5,z19,z6]),(0,[z0,z2,z636,z3,z4,z5,z6]),(0,[z637,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z638,z3,z4,z5,z6])]],
   [[(0,[z158,z0,z2,z3,z4,z204,z6]),(0,[z0,z2,z3,z4,z639,z5,z6])],[(0,[z640,z0,z2,z3,z4,z5,z6]),(0,[z158,z0,z2,z125,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z641]),(0,[z0,z2,z3,z4,z642,z5,z6]),(0,[z0,z2,z3,z4,z643,z5,z6]),(0,[z0,z2,z3,z4,z644,z5,z6])],[(0,[z645,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z19,z78,z6]),(1,[z0,z2,z3,z4,z646,z6])],[(0,[z0,z2,z647,z3,z4,z5,z6])],[(0,[z0,z123,z2,z3,z4,z206,z6]),(0,[z648,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z649,z6]),(0,[z0,z2,z3,z4,z5,z650,z6]),(0,[z0,z42,z2,z3,z4,z174,z6])],[(0,[z0,z28,z125,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z651,z6]),(1,[z0,z2,z240,z4,z5,z29])],[(0,[z0,z2,z3,z652,z4,z5,z6]),(0,[z10,z123,z2,z3,z4,z5,z6]),(0,[z0,z653,z2,z3,z4,z5,z6]),(0,[z23,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z170,z3,z4,z5,z6])]],
   [[(0,[z54,z0,z2,z71,z4,z5,z6]),(0,[z0,z2,z36,z4,z5,z66,z6]),(0,[z0,z2,z71,z4,z34,z5,z6]),(0,[z0,z2,z3,z4,z654,z5,z6]),(0,[z75,z465,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z655,z6]),(0,[z0,z2,z3,z4,z5,z223,z6]),(1,[z99,z0,z2,z4,z5,z262]),(0,[z0,z2,z3,z4,z656,z5,z6])],[(0,[z0,z2,z3,z545,z4,z5,z6]),(0,[z2,z3,z107,z4,z13,z5,z6]),(0,[z657,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z658,z5,z6])],[(0,[z14,z2,z3,z4,z5,z21,z6]),(0,[z465,z0,z2,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z4,z646,z6]),(0,[z0,z2,z3,z4,z659,z5,z6])],[(0,[z0,z2,z208,z71,z4,z5,z6]),(0,[z0,z2,z3,z660,z4,z5,z6]),(0,[z0,z2,z3,z267,z34,z5,z6]),(0,[z99,z0,z2,z4,z34,z5,z6]),(1,[z184,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z174,z5,z67]),(0,[z0,z2,z661,z3,z4,z5,z6])],[(0,[z662,z0,z2,z3,z4,z5,z6]),(0,[z60,z0,z598,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z5,z21]),(0,[z663,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z664,z6]),(0,[z0,z665,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z666,z6]),(1,[z0,z2,z3,z4,z5,z199])],[(0,[z0,z667,z2,z3,z4,z5,z6]),(0,[z0,z2,z668,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z669,z6])],[(0,[z359,z0,z2,z3,z4,z5,z6]),(0,[z670,z0,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z274,z4,z6]),(1,[z159,z0,z2,z3,z4,z5]),(1,[z0,z2,z3,z4,z301,z6]),(0,[z0,z2,z3,z4,z5,z6,z671])],[(0,[z258,z0,z2,z3,z4,z5,z6]),(0,[z134,z0,z2,z3,z4,z5,z6]),(0,[z52,z0,z2,z3,z4,z5,z6]),(0,[z672,z0,z2,z3,z4,z5,z6]),(0,[z75,z0,z2,z3,z4,z486,z6])]],
   [[(0,[z0,z2,z598,z3,z4,z5,z6]),(1,[z0,z2,z61,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z673,z6]),(0,[z23,z168,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z674,z5,z6]),(1,[z0,z2,z69,z3,z5,z39])],[(0,[z0,z197,z123,z3,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z22,z6]),(1,[z0,z2,z3,z4,z5,z471]),(0,[z675,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z267,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z676,z6]),(0,[z0,z2,z3,z4,z5,z6,z677]),(0,[z0,z2,z3,z4,z8,z5,z6])],[(0,[z678,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z679,z6]),(0,[z0,z2,z3,z680,z4,z5,z6]),(0,[z0,z366,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z681,z5,z6]),(0,[z99,z0,z2,z3,z4,z5,z262]),(0,[z82,z0,z2,z3,z4,z78,z6]),(0,[z0,z2,z3,z274,z4,z94,z6]),(1,[z0,z2,z3,z38,z5,z202]),(0,[z0,z42,z2,z3,z4,z165,z5])],[(0,[z682,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z61,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z43,z6]),(0,[z0,z28,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z683,z6]),(0,[z0,z2,z3,z4,z684,z5,z6])],[(0,[z0,z685,z2,z3,z4,z5,z6]),(0,[z0,z2,z240,z3,z4,z5,z262]),(0,[z0,z686,z2,z3,z4,z5,z6])],[(0,[z0,z687,z2,z3,z4,z5,z6]),(0,[z60,z2,z3,z4,z5,z117,z6]),(0,[z0,z2,z3,z4,z688,z5,z6]),(0,[z0,z2,z3,z4,z689,z5,z6])],[(0,[z0,z690,z2,z3,z4,z5,z6]),(0,[z0,z2,z125,z4,z34,z5,z6]),(0,[z0,z2,z3,z4,z5,z691,z6]),(0,[z82,z0,z2,z3,z274,z5,z6]),(0,[z0,z2,z3,z38,z5,z6,z202])]],
   [[(0,[z0,z2,z3,z4,z692,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z0,z2,z3,z34,z5,z6,z202])],[(1,[z54,z2,z36,z4,z5,z6]),(0,[z0,z2,z3,z4,z693,z5,z6]),(0,[z0,z2,z3,z694,z4,z5,z6]),(0,[z0,z2,z3,z695,z4,z5,z6]),(0,[z0,z696,z2,z3,z4,z5,z6])],[(1,[z10,z123,z3,z4,z5,z6]),(1,[z0,z407,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z697,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z698,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z699]),(0,[z0,z2,z700,z3,z4,z5,z6]),(0,[z0,z2,z3,z592,z4,z5,z6]),(0,[z701,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z5,z39])],[(0,[z63,z0,z2,z545,z4,z5,z6]),(1,[z573,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z29,z6,z262])],[(0,[z0,z2,z208,z125,z4,z5,z6]),(0,[z702,z0,z2,z3,z4,z5,z6]),(1,[z82,z0,z2,z3,z78,z6])],[(0,[z703,z0,z2,z3,z4,z5,z6])],[(0,[z704,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z705]),(0,[z0,z2,z3,z4,z5,z706,z6]),(0,[z0,z2,z3,z4,z43,z66,z6]),(0,[z75,z0,z2,z3,z177,z5,z6]),(0,[z0,z2,z3,z4,z5,z646,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z487,z2,z71,z4,z5,z6]),(0,[z0,z2,z707,z4,z5,z6]),(0,[z0,z2,z3,z708,z5,z6]),(0,[z0,z241,z3,z120,z5,z6]),(0,[z82,z0,z81,z3,z78,z6])],[(0,[z0,z2,z709,z4,z5,z6]),(0,[z0,z2,z279,z4,z5,z6]),(0,[z0,z2,z3,z260,z22,z6]),(0,[z0,z2,z3,z4,z5,z710])],[(0,[z0,z2,z3,z4,z711,z6]),(0,[z134,z0,z2,z3,z4,z6]),(0,[z60,z2,z397,z4,z117,z6]),(0,[z712,z2,z3,z4,z5,z6]),(0,[z0,z251,z3,z4,z5,z138])],[(0,[z0,z2,z3,z4,z713,z6]),(0,[z60,z2,z3,z4,z117,z266]),(0,[z414,z2,z3,z4,z5,z568])],[(0,[z522,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z714,z6]),(0,[z258,z2,z3,z4,z286,z6]),(0,[z0,z2,z715,z4,z5,z6]),(0,[z0,z28,z340,z4,z5,z6]),(0,[z23,z0,z257,z8,z5,z6]),(0,[z0,z2,z520,z34,z5,z6])],[(0,[z0,z2,z3,z4,z716,z6]),(0,[z201,z2,z36,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z717]),(0,[z0,z2,z3,z97,z204,z6]),(0,[z0,z2,z4,z5,z29,z641]),(0,[z23,z0,z3,z8,z24,z6]),(0,[z718,z2,z3,z4,z5,z6])],[(0,[z0,z2,z719,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z720]),(0,[z0,z721,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z137]),(0,[z0,z2,z3,z4,z5,z722])],[(0,[z0,z2,z3,z4,z723,z6]),(0,[z191,z121,z3,z4,z5,z6]),(0,[z629,z2,z3,z4,z5,z11]),(0,[z0,z724,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z725,z6]),(0,[z168,z2,z3,z4,z5,z72]),(0,[z0,z2,z3,z4,z5,z726])]],
   [[(0,[z161,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z727,z5,z6]),(0,[z63,z2,z279,z65,z5,z6]),(0,[z184,z2,z3,z108,z5,z6]),(0,[z0,z2,z3,z4,z728,z6]),(0,[z465,z2,z3,z221,z5,z6]),(0,[z0,z2,z729,z4,z5,z6])],[(0,[z60,z2,z3,z4,z117,z6]),(0,[z184,z2,z3,z4,z13,z6]),(0,[z52,z2,z3,z260,z5,z6]),(0,[z0,z2,z464,z34,z5,z6]),(0,[z573,z1,z3,z4,z5,z6])],[(0,[z0,z2,z3,z730,z5,z6]),(0,[z731,z2,z3,z4,z5,z6]),(0,[z76,z2,z3,z4,z486,z6]),(0,[z82,z184,z2,z3,z78,z6])],[(0,[z0,z2,z3,z4,z5,z732]),(0,[z0,z685,z125,z4,z5,z6]),(0,[z733,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z8,z5,z199]),(0,[z75,z0,z4,z5,z302,z80]),(1,[z85,z2,z3,z78,z6])],[(0,[z0,z407,z3,z4,z5,z238]),(0,[z0,z2,z545,z4,z167,z6]),(0,[z239,z2,z3,z4,z204,z6]),(0,[z158,z159,z0,z41,z4,z5]),(0,[z0,z2,z3,z4,z5,z734]),(0,[z414,z81,z3,z4,z5,z6]),(0,[z414,z2,z592,z4,z5,z6])],[(0,[z0,z2,z735,z4,z5,z6]),(0,[z134,z0,z2,z736,z4,z6]),(0,[z0,z2,z61,z108,z5,z6]),(0,[z737,z2,z3,z4,z5,z6]),(0,[z0,z738,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z739,z6])],[(1,[z740,z3,z4,z5,z6]),(0,[z10,z653,z3,z4,z5,z6]),(0,[z0,z741,z3,z4,z5,z6]),(0,[z742,z2,z3,z4,z5,z6]),(0,[z198,z2,z3,z4,z19,z6]),(0,[z743,z2,z3,z4,z5,z6]),(0,[z99,z0,z2,z34,z5,z202]),(0,[z744,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z745,z6]),(0,[z0,z2,z3,z4,z5,z746]),(0,[z60,z2,z3,z694,z4,z6]),(0,[z0,z747,z3,z4,z5,z6]),(0,[z0,z2,z61,z4,z5,z116]),(0,[z158,z0,z41,z4,z22,z6]),(0,[z0,z41,z4,z5,z6,z471]),(0,[z0,z2,z3,z4,z748,z6]),(0,[z749,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z527,z5,z202]),(0,[z0,z2,z3,z4,z174,z67])]],
   [[(0,[z75,z0,z340,z3,z4,z5]),(0,[z0,z750,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z751,z6]),(0,[z134,z0,z2,z752,z4,z6]),(0,[z0,z753,z3,z4,z5,z6]),(0,[z328,z754,z2,z4,z5,z6]),(0,[z331,z0,z2,z4,z755,z6])],[(0,[z0,z2,z3,z4,z756,z6]),(0,[z0,z757,z3,z4,z5,z6]),(0,[z0,z2,z3,z758,z5,z6]),(0,[z0,z2,z3,z759,z4,z5])],[(0,[z0,z2,z3,z4,z5,z760]),(0,[z203,z3,z4,z13,z5,z6]),(1,[z2,z3,z65,z286,z6]),(0,[z0,z28,z761,z4,z5,z6]),(0,[z0,z3,z4,z8,z24,z6]),(0,[z0,z2,z762,z4,z5,z6])],[(0,[z0,z2,z3,z4,z763,z6]),(0,[z0,z764,z3,z4,z5,z6]),(0,[z0,z455,z3,z4,z43,z6]),(0,[z701,z2,z3,z4,z5,z21]),(0,[z0,z2,z3,z4,z132,z6]),(0,[z328,z765,z2,z4,z5,z6]),(0,[z0,z2,z434,z3,z5,z39])],[(0,[z0,z455,z3,z4,z122,z6]),(0,[z60,z2,z3,z4,z286,z6]),(0,[z0,z2,z766,z4,z5,z6]),(0,[z0,z2,z3,z4,z767,z6]),(0,[z366,z2,z188,z4,z5,z6]),(0,[z197,z573,z3,z4,z43,z6]),(0,[z0,z2,z3,z4,z5,z768]),(0,[z0,z2,z33,z4,z129,z6])],[(0,[z0,z2,z3,z97,z22,z6]),(0,[z0,z2,z3,z267,z5,z135]),(0,[z23,z0,z3,z8,z301,z6]),(0,[z0,z2,z4,z5,z29,z722]),(0,[z0,z2,z3,z38,z5,z739])],[(0,[z0,z2,z769,z4,z5,z6]),(0,[z0,z2,z3,z4,z770,z6]),(0,[z0,z3,z350,z4,z5,z80]),(0,[z0,z2,z4,z5,z755,z6]),(0,[z0,z340,z3,z4,z100,z6]),(0,[z0,z2,z69,z3,z5,z39])]],
   [[(0,[z0,z2,z3,z4,z204,z6]),(0,[z0,z2,z3,z4,z5,z771])],[(0,[z0,z2,z3,z4,z206,z6]),(0,[z0,z2,z772,z4,z5,z6]),(0,[z0,z773,z3,z4,z5,z6]),(0,[z134,z85,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z24,z72]),(0,[z75,z0,z3,z4,z486,z80])],[(0,[z0,z2,z3,z108,z5,z116]),(0,[z774,z2,z3,z4,z5,z6]),(0,[z76,z2,z3,z177,z5,z6]),(0,[z0,z2,z3,z775,z5,z6]),(0,[z0,z2,z3,z776,z5,z6]),(0,[z777,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z38,z5,z202])],[(0,[z0,z2,z3,z778,z5,z6]),(0,[z0,z779,z3,z4,z5,z6]),(0,[z0,z2,z3,z780,z5,z6])],[(0,[z0,z2,z781,z4,z5,z6]),(0,[z0,z2,z3,z4,z646,z202]),(0,[z184,z2,z782,z4,z5,z6])],[(0,[z198,z2,z3,z4,z5,z6]),(0,[z2,z3,z107,z783,z5,z6]),(0,[z239,z2,z3,z4,z22,z6]),(0,[z0,z3,z4,z5,z6,z784]),(0,[z785,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z786,z6]),(0,[z258,z2,z3,z284,z5,z6]),(0,[z0,z2,z3,z4,z5,z787]),(0,[z366,z2,z3,z4,z5,z135]),(0,[z0,z2,z257,z4,z24,z6]),(0,[z0,z2,z3,z264,z5,z202]),(0,[z0,z2,z3,z788,z5,z6])],[(0,[z0,z2,z3,z4,z167,z64]),(0,[z60,z455,z3,z4,z117,z6]),(0,[z0,z125,z761,z4,z5,z6]),(0,[z789,z2,z3,z4,z5,z6]),(0,[z0,z2,z350,z4,z5,z138]),(0,[z0,z2,z4,z129,z755,z6]),(0,[z0,z2,z790,z4,z5,z6])]],
   [[(0,[z2,z740,z3,z4,z5,z6]),(0,[z0,z2,z791,z4,z5,z6])],[(0,[z0,z407,z3,z4,z5,z6]),(0,[z103,z2,z3,z4,z117,z6]),(0,[z0,z2,z3,z260,z5,z137]),(0,[z0,z2,z3,z4,z5,z792]),(0,[z184,z2,z3,z274,z4,z6])],[(0,[z0,z2,z3,z4,z793,z6]),(0,[z0,z2,z794,z4,z5,z6]),(0,[z0,z242,z3,z4,z5,z6]),(0,[z0,z2,z398,z4,z5,z29]),(0,[z99,z313,z2,z4,z5,z262])],[(0,[z0,z2,z3,z4,z795,z6]),(0,[z0,z2,z796,z4,z5,z6]),(0,[z385,z2,z3,z4,z5,z202]),(0,[z82,z0,z2,z3,z78,z6]),(0,[z797,z2,z3,z4,z5,z6])],[(0,[z0,z598,z61,z4,z5,z6]),(0,[z328,z0,z2,z4,z5,z471]),(0,[z798,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z43,z799,z6]),(0,[z313,z2,z3,z4,z100,z6]),(0,[z0,z340,z3,z120,z5,z6])],[(0,[z0,z2,z800,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z801])],[(0,[z184,z2,z3,z65,z5,z6]),(0,[z60,z2,z3,z4,z32,z6])],[(0,[z0,z802,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z803]),(0,[z184,z2,z3,z4,z43,z6])]],
   [[(0,[z63,z407,z3,z65,z5,z6]),(0,[z2,z3,z107,z13,z78,z6]),(0,[z0,z2,z804,z4,z5,z6]),(0,[z0,z2,z170,z7,z5,z6]),(0,[z0,z2,z3,z4,z755,z6]),(0,[z2,z3,z4,z5,z6,z805])],[(0,[z0,z2,z3,z4,z22,z6]),(0,[z0,z2,z188,z4,z5,z6]),(0,[z0,z2,z3,z4,z806,z6]),(0,[z198,z197,z3,z4,z43,z6]),(0,[z0,z2,z240,z350,z4,z5]),(0,[z75,z0,z3,z177,z5,z80])],[(0,[z0,z2,z279,z4,z167,z6]),(0,[z0,z2,z3,z4,z807,z6]),(0,[z0,z312,z3,z4,z19,z6]),(0,[z0,z2,z3,z4,z301,z72]),(0,[z0,z30,z3,z4,z19,z6]),(0,[z0,z2,z762,z34,z5,z6])],[(0,[z0,z2,z3,z808,z5,z6])],[(1,[z2,z3,z108,z117,z6]),(0,[z99,z0,z340,z4,z5,z262])],[(0,[z236,z2,z36,z4,z5,z6]),(0,[z0,z203,z3,z4,z286,z6]),(0,[z0,z2,z761,z4,z5,z6])],[(0,[z2,z121,z3,z4,z5,z266]),(0,[z10,z2,z397,z4,z5,z6]),(0,[z0,z1,z3,z267,z5,z6]),(0,[z0,z2,z290,z7,z5,z6])],[(0,[z0,z2,z3,z4,z5,z809]),(0,[z10,z2,z3,z4,z5,z266]),(0,[z0,z2,z3,z4,z5,z810]),(0,[z0,z598,z3,z108,z5,z6]),(0,[z158,z0,z41,z4,z5,z137]),(0,[z0,z2,z373,z34,z5,z6]),(0,[z0,z2,z257,z4,z301,z6]),(0,[z0,z2,z811,z4,z5,z6]),(0,[z465,z2,z3,z4,z132,z6])]],
   [[(0,[z0,z812,z3,z4,z5,z6]),(0,[z0,z3,z267,z813,z5,z6]),(0,[z0,z1,z3,z112,z5,z6]),(0,[z99,z0,z2,z4,z646,z262])],[(0,[z0,z2,z3,z4,z814,z6]),(0,[z0,z598,z3,z4,z5,z116]),(0,[z0,z2,z3,z815,z5,z6]),(0,[z0,z2,z3,z816,z5,z6]),(0,[z573,z3,z4,z8,z5,z6]),(0,[z0,z2,z3,z4,z642,z67]),(0,[z2,z3,z4,z5,z817,z6]),(0,[z313,z2,z3,z120,z5,z6]),(0,[z0,z81,z3,z4,z5,z375]),(0,[z0,z2,z592,z4,z5,z375])],[(0,[z0,z818,z3,z4,z5,z6]),(0,[z60,z84,z2,z3,z4,z6]),(0,[z159,z0,z340,z3,z4,z5]),(0,[z168,z2,z188,z4,z5,z6]),(0,[z85,z2,z3,z4,z5,z375]),(0,[z184,z819,z3,z4,z5,z6])],[(0,[z198,z455,z3,z4,z5,z6]),(0,[z0,z2,z3,z260,z204,z6]),(0,[z820,z2,z3,z4,z5,z6]),(0,[z158,z0,z340,z4,z5,z6]),(0,[z0,z2,z3,z4,z821,z6]),(0,[z385,z2,z4,z34,z5,z6]),(0,[z0,z2,z3,z274,z822,z6])],[(0,[z359,z740,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z823,z6]),(0,[z134,z0,z2,z3,z108,z6]),(0,[z0,z2,z125,z260,z5,z6]),(0,[z0,z2,z3,z4,z100,z6]),(0,[z824,z2,z3,z4,z5,z6]),(0,[z82,z2,z3,z396,z78,z6]),(0,[z0,z2,z69,z31,z5,z39])],[(0,[z159,z0,z2,z3,z4,z806]),(0,[z99,z0,z2,z3,z177,z5])],[(0,[z0,z2,z3,z97,z5,z137]),(0,[z0,z2,z3,z4,z825,z6]),(0,[z0,z2,z3,z4,z5,z826]),(0,[z366,z1,z3,z4,z5,z6]),(0,[z313,z340,z3,z4,z5,z6])],[(0,[z0,z2,z3,z108,z43,z6]),(0,[z0,z2,z293,z4,z5,z6]),(0,[z827,z2,z3,z4,z5,z6]),(0,[z828,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z497,z5,z202]),(0,[z0,z2,z240,z4,z5,z722]),(0,[z0,z2,z240,z4,z5,z514])]],
   [[(0,[z2,z3,z4,z13,z235,z6]),(0,[z0,z2,z3,z4,z5,z829]),(0,[z830,z2,z3,z4,z5,z6])],[(0,[z0,z3,z761,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z831]),(0,[z328,z75,z0,z2,z4,z5]),(0,[z0,z2,z579,z4,z5,z29]),(0,[z99,z0,z2,z4,z5,z162]),(0,[z0,z2,z557,z4,z129,z6]),(0,[z0,z340,z3,z4,z5,z29]),(0,[z0,z2,z592,z4,z5,z568])],[(0,[z0,z2,z3,z832,z5,z6]),(0,[z0,z2,z3,z4,z833,z5]),(0,[z0,z2,z3,z4,z834,z6]),(0,[z0,z550,z3,z267,z5,z6]),(0,[z82,z85,z2,z3,z78,z6]),(0,[z414,z242,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z835,z6])],[(0,[z0,z2,z4,z5,z6,z836]),(0,[z530,z0,z2,z3,z78,z6]),(0,[z0,z2,z3,z837,z5,z6]),(0,[z0,z2,z240,z623,z4,z5]),(0,[z0,z838,z3,z4,z5,z6])],[(0,[z839,z0,z2,z3,z4,z6]),(0,[z2,z3,z4,z65,z286,z6]),(0,[z0,z2,z3,z840,z5,z6]),(0,[z159,z0,z2,z240,z4,z5]),(0,[z0,z2,z4,z34,z5,z223])],[(0,[z0,z2,z3,z4,z5,z841]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z0,z2,z3,z4,z843,z6]),(0,[z0,z2,z3,z120,z5,z39]),(0,[z0,z2,z3,z4,z835,z174])],[(0,[z0,z2,z3,z4,z5,z844]),(0,[z0,z106,z3,z4,z19,z6]),(0,[z328,z75,z0,z4,z5,z80])],[(0,[z0,z2,z3,z4,z845,z6]),(0,[z0,z2,z3,z813,z5,z6])]],
   [[(0,[z0,z846,z3,z4,z5,z6]),(0,[z562,z2,z3,z4,z5,z11]),(0,[z0,z28,z4,z5,z6,z494]),(0,[z0,z275,z125,z4,z5,z6]),(0,[z99,z0,z2,z4,z5,z490])],[(0,[z158,z0,z41,z4,z204,z6]),(0,[z0,z2,z3,z120,z5,z6])],[(0,[z60,z2,z3,z108,z117,z6]),(0,[z158,z0,z761,z4,z5,z6]),(0,[z0,z2,z3,z847,z5,z6]),(0,[z23,z0,z3,z8,z5,z72]),(0,[z0,z340,z3,z4,z5,z39]),(0,[z0,z81,z592,z4,z5,z6])],[(0,[z0,z1,z3,z4,z206,z6]),(0,[z60,z2,z3,z4,z848,z6]),(0,[z0,z2,z3,z4,z5,z849]),(0,[z0,z2,z3,z850,z5,z6]),(0,[z0,z2,z851,z4,z5,z6]),(0,[z0,z197,z3,z4,z617,z6]),(0,[z0,z2,z852,z4,z5,z6]),(0,[z0,z2,z3,z4,z853,z6]),(0,[z85,z2,z592,z4,z5,z6])],[(0,[z134,z2,z3,z107,z4,z6]),(0,[z60,z2,z3,z4,z117,z116]),(0,[z854,z2,z3,z4,z5,z6]),(0,[z0,z2,z188,z4,z24,z6])],[(0,[z0,z2,z855,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z856]),(0,[z0,z226,z3,z4,z5,z857])],[(0,[z0,z2,z3,z858,z5,z6]),(0,[z0,z203,z3,z4,z5,z238]),(0,[z0,z340,z3,z4,z5,z6]),(0,[z859,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z177,z132,z6]),(0,[z860,z2,z3,z4,z5,z6]),(0,[z99,z385,z2,z4,z5,z262])],[(0,[z0,z3,z4,z5,z857,z80])]],
   [[(0,[z0,z861,z3,z4,z5,z6])],[(0,[z0,z2,z3,z862,z5,z6]),(0,[z0,z863,z3,z4,z5,z6]),(0,[z564,z0,z3,z8,z5,z6])],[(0,[z0,z407,z3,z4,z167,z6]),(0,[z0,z2,z350,z4,z5,z6]),(0,[z704,z0,z3,z4,z5,z80]),(0,[z328,z0,z2,z4,z5,z202]),(0,[z864,z2,z3,z4,z5,z6])],[(0,[z10,z455,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z865,z6]),(0,[z0,z2,z3,z695,z5,z202]),(0,[z0,z866,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z363,z67])],[(0,[z455,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z475,z5,z202]),(0,[z0,z2,z154,z4,z5,z6]),(0,[z867,z2,z3,z4,z5,z6]),(0,[z0,z2,z69,z3,z5,z223])],[(0,[z85,z2,z3,z5,z78,z6]),(0,[z0,z2,z170,z4,z5,z39])],[(0,[z0,z2,z3,z4,z5,z238]),(0,[z0,z2,z3,z4,z19,z266]),(0,[z0,z2,z350,z4,z5,z80])],[(0,[z366,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z783,z5,z6]),(0,[z868,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z120,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z869,z6]),(0,[z0,z2,z3,z4,z5,z870]),(0,[z0,z2,z3,z871,z5,z6]),(0,[z0,z2,z33,z4,z681,z6]),(0,[z872,z2,z3,z4,z5,z6])],[(0,[z0,z873,z3,z4,z5,z6]),(0,[z0,z2,z279,z4,z5,z64]),(0,[z0,z455,z3,z180,z5,z6]),(0,[z0,z2,z170,z4,z5,z6])],[(0,[z0,z2,z874,z4,z5,z6]),(0,[z465,z2,z293,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z875])],[(0,[z0,z2,z3,z4,z5,z876]),(0,[z60,z2,z3,z107,z274,z6]),(0,[z0,z2,z3,z274,z692,z6]),(0,[z0,z2,z517,z34,z5,z6])],[(0,[z0,z877,z3,z4,z5,z6]),(0,[z0,z2,z878,z4,z5,z6]),(0,[z0,z2,z3,z4,z879,z6]),(0,[z0,z2,z3,z4,z880,z6]),(0,[z0,z340,z208,z4,z5,z6])],[(0,[z63,z2,z3,z65,z5,z238]),(0,[z0,z2,z881,z4,z5,z6]),(0,[z2,z3,z4,z108,z117,z6]),(0,[z0,z2,z3,z4,z549,z67]),(0,[z882,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z883,z6]),(0,[z319,z0,z3,z8,z5,z6]),(0,[z328,z0,z340,z4,z5,z6]),(0,[z884,z0,z3,z4,z5,z6]),(0,[z313,z241,z3,z4,z5,z6])],[(0,[z147,z2,z3,z65,z5,z6]),(0,[z0,z2,z3,z4,z5,z885]),(0,[z76,z2,z3,z4,z132,z6])],[]],
   [[(0,[z0,z2,z3,z4,z51,z6]),(0,[z0,z2,z3,z886,z5,z6]),(0,[z0,z2,z3,z4,z22,z471]),(0,[z0,z2,z3,z4,z5,z887])],[(0,[z740,z121,z3,z4,z5,z6]),(0,[z10,z740,z3,z4,z5,z6]),(0,[z0,z2,z888,z4,z5,z6]),(0,[z60,z598,z3,z4,z117,z6]),(0,[z0,z2,z4,z5,z6,z889]),(0,[z0,z2,z293,z4,z486,z6]),(0,[z0,z2,z3,z4,z890,z6]),(0,[z0,z2,z3,z891,z5,z6])],[(0,[z0,z892,z3,z4,z5,z6]),(0,[z0,z2,z893,z4,z5,z6]),(1,[z0,z41,z4,z5,z471]),(0,[z159,z0,z2,z3,z4,z883]),(0,[z894,z2,z3,z4,z5,z6]),(0,[z0,z2,z895,z4,z5,z6])],[(0,[z0,z203,z3,z4,z5,z6]),(0,[z134,z0,z2,z3,z4,z896]),(0,[z0,z2,z257,z4,z5,z72]),(0,[z0,z2,z3,z221,z132,z6]),(0,[z328,z0,z226,z2,z4,z5]),(0,[z82,z0,z2,z592,z78,z6])],[(0,[z158,z52,z41,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z897]),(0,[z0,z2,z898,z4,z5,z6]),(0,[z385,z2,z3,z4,z100,z6])],[(0,[z0,z2,z260,z5,z29,z6]),(0,[z0,z28,z4,z5,z29,z80]),(0,[z0,z2,z899,z4,z5,z6])],[(0,[z0,z2,z3,z900,z5,z6]),(0,[z0,z901,z3,z4,z5,z6]),(0,[z0,z407,z545,z4,z5,z6]),(0,[z159,z902,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z903,z6]),(0,[z0,z904,z3,z4,z5,z6]),(0,[z0,z242,z3,z4,z5,z375])]],
   [[(0,[z0,z2,z3,z4,z5,z905]),(0,[z0,z2,z3,z906,z5,z6]),(0,[z52,z2,z3,z4,z5,z471]),(0,[z907,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z799,z6]),(0,[z0,z197,z3,z4,z799,z6]),(0,[z0,z908,z3,z4,z5,z6]),(0,[z82,z0,z2,z3,z78,z375])],[(0,[z0,z909,z3,z4,z5,z6]),(0,[z910,z2,z3,z4,z5,z6])],[(0,[z63,z203,z3,z65,z5,z6]),(0,[z328,z0,z2,z4,z5,z262]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z120,z646,z6]),(0,[z0,z2,z3,z5,z739,z202])],[(0,[z0,z2,z912,z4,z5,z6]),(0,[z10,z156,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z286,z238]),(0,[z913,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z914]),(0,[z0,z2,z3,z4,z915,z6]),(0,[z184,z2,z3,z107,z5,z6]),(0,[z0,z2,z188,z8,z5,z6]),(0,[z0,z2,z3,z4,z916,z6]),(0,[z414,z2,z154,z4,z5,z6]),(0,[z0,z2,z917,z4,z5,z6])],[(0,[z918,z2,z3,z4,z5,z6]),(0,[z0,z241,z3,z4,z5,z6]),(0,[z23,z168,z3,z8,z5,z6]),(0,[z75,z0,z3,z4,z132,z80]),(0,[z328,z0,z2,z4,z890,z6]),(0,[z0,z2,z3,z173,z100,z6])],[(0,[z919,z2,z3,z4,z5,z6])],[(0,[z147,z0,z3,z8,z5,z6]),(0,[z0,z2,z3,z4,z5,z920]),(0,[z921,z2,z3,z4,z5,z6]),(0,[z0,z2,z922,z4,z5,z6]),(0,[z0,z2,z700,z34,z5,z6]),(0,[z99,z0,z2,z120,z5,z262]),(0,[z0,z242,z3,z4,z5,z568]),(0,[z923,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z924,z36,z4,z5,z6]),(0,[z0,z203,z3,z4,z5,z64]),(0,[z2,z3,z4,z13,z286,z6]),(0,[z328,z0,z28,z4,z5,z6]),(0,[z0,z2,z170,z34,z5,z6]),(0,[z82,z414,z2,z3,z78,z6]),(0,[z0,z81,z3,z4,z78,z6]),(0,[z82,z0,z2,z3,z78,z568]),(0,[z0,z925,z3,z4,z5,z6]),(0,[z926,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z927,z6]),(0,[z0,z2,z928,z4,z5,z6]),(0,[z0,z2,z3,z4,z929,z6]),(0,[z0,z1,z3,z813,z5,z6]),(0,[z0,z2,z293,z177,z5,z6]),(0,[z328,z0,z2,z775,z5,z6]),(0,[z328,z0,z2,z776,z5,z6]),(0,[z0,z930,z3,z4,z5,z6]),(0,[z385,z2,z3,z120,z5,z6])],[(0,[z0,z931,z3,z4,z5,z6]),(0,[z134,z63,z2,z3,z4,z6]),(0,[z0,z455,z3,z4,z19,z6]),(0,[z0,z2,z240,z4,z5,z664]),(0,[z366,z2,z3,z4,z24,z6]),(0,[z0,z42,z2,z3,z4,z551]),(0,[z0,z2,z3,z177,z5,z138]),(1,[z0,z3,z4,z5,z857]),(0,[z0,z2,z3,z4,z5,z932])],[(0,[z0,z2,z3,z4,z5,z933]),(0,[z0,z3,z4,z8,z206,z6]),(0,[z0,z2,z3,z4,z934,z6]),(0,[z0,z2,z601,z3,z5,z39]),(0,[z0,z2,z3,z935,z5,z6]),(0,[z0,z2,z3,z4,z936,z6]),(0,[z0,z937,z3,z4,z5,z6])],[(0,[z60,z121,z3,z4,z19,z6]),(0,[z534,z2,z3,z107,z5,z6]),(0,[z0,z2,z3,z4,z5,z938]),(0,[z2,z3,z4,z5,z939,z6]),(0,[z0,z2,z940,z4,z5,z6]),(0,[z0,z2,z69,z3,z5,z739])],[(0,[z0,z2,z3,z4,z5,z941]),(0,[z23,z0,z188,z8,z5,z6]),(0,[z0,z2,z3,z8,z5,z135]),(0,[z0,z942,z3,z4,z5,z6]),(0,[z85,z2,z3,z274,z5,z6])],[(0,[z0,z2,z943,z4,z5,z6]),(0,[z10,z2,z3,z108,z5,z6]),(0,[z0,z2,z924,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z944]),(0,[z523,z0,z41,z4,z5,z6]),(0,[z0,z28,z605,z4,z5,z6]),(0,[z0,z2,z120,z34,z5,z6]),(0,[z385,z340,z3,z4,z5,z6]),(0,[z0,z42,z2,z3,z4,z835])],[(0,[z0,z2,z3,z4,z945,z6]),(0,[z134,z0,z946,z3,z4,z6]),(0,[z0,z2,z3,z947,z5,z6]),(0,[z0,z197,z3,z4,z43,z6]),(0,[z0,z2,z4,z34,z646,z6]),(0,[z948,z2,z3,z4,z5,z6]),(0,[z0,z582,z2,z3,z4,z165])]],
   [[(0,[z2,z121,z397,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z949]),(0,[z0,z242,z592,z4,z5,z6]),(0,[z82,z184,z2,z3,z4,z6])],[(0,[z0,z407,z3,z4,z5,z64]),(0,[z52,z2,z3,z4,z22,z6])],[(0,[z0,z3,z4,z405,z19,z6]),(0,[z0,z2,z3,z120,z5,z223])],[(0,[z70,z2,z71,z4,z5,z6]),(0,[z0,z455,z3,z4,z5,z266]),(0,[z950,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z512,z67])],[(0,[z0,z2,z3,z4,z951,z6]),(0,[z0,z2,z3,z53,z4,z5]),(0,[z0,z2,z3,z952,z5,z6])],[(0,[z0,z2,z3,z4,z5,z953]),(0,[z0,z2,z208,z364,z5,z6]),(0,[z0,z2,z3,z4,z5,z135]),(0,[z198,z2,z3,z4,z43,z6]),(0,[z0,z42,z2,z3,z4,z311])],[(0,[z0,z2,z3,z4,z5,z954]),(0,[z0,z955,z3,z4,z5,z6]),(0,[z615,z0,z41,z4,z5,z6]),(0,[z956,z2,z3,z4,z5,z6]),(0,[z331,z0,z2,z4,z66,z6])],[(0,[z288,z121,z3,z4,z5,z6]),(0,[z0,z2,z397,z180,z5,z6]),(0,[z0,z2,z3,z4,z957,z6]),(0,[z0,z340,z3,z173,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z286,z6]),(0,[z0,z2,z3,z180,z5,z266])],[(0,[z0,z455,z3,z4,z5,z6]),(0,[z0,z2,z958,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z959]),(0,[z0,z2,z3,z960,z5,z6]),(0,[z76,z2,z293,z4,z5,z6]),(0,[z184,z738,z3,z4,z5,z6])],[(0,[z10,z123,z3,z4,z122,z6]),(0,[z60,z2,z61,z4,z117,z6]),(0,[z99,z0,z2,z260,z5,z6])],[(0,[z366,z2,z3,z4,z301,z6])],[(0,[z0,z407,z279,z4,z5,z6]),(0,[z99,z704,z0,z2,z4,z5]),(0,[z0,z81,z3,z4,z5,z568])],[(0,[z961,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z515,z5,z202]),(0,[z0,z962,z3,z4,z5,z6]),(0,[z85,z2,z3,z4,z5,z568])],[(0,[z0,z2,z3,z963,z5,z6]),(0,[z0,z2,z3,z180,z5,z6]),(0,[z12,z2,z3,z108,z5,z6]),(0,[z0,z2,z3,z260,z5,z6]),(0,[z0,z2,z3,z4,z964,z6]),(0,[z23,z366,z3,z8,z5,z6]),(0,[z168,z2,z3,z4,z5,z135]),(0,[z0,z2,z3,z4,z965,z6]),(0,[z0,z2,z3,z966,z5,z6]),(0,[z0,z2,z3,z626,z94,z6]),(0,[z0,z2,z293,z221,z5,z6]),(0,[z0,z2,z3,z4,z967,z6])],[(0,[z63,z2,z3,z65,z286,z6]),(0,[z0,z2,z3,z4,z5,z968]),(0,[z0,z2,z3,z4,z5,z969]),(0,[z159,z0,z2,z350,z4,z5]),(0,[z0,z970,z3,z4,z5,z6])]],
   [[(0,[z971,z2,z3,z4,z5,z6]),(0,[z972,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z973]),(0,[z0,z458,z2,z3,z4,z165]),(0,[z0,z2,z188,z4,z5,z72]),(0,[z0,z974,z3,z4,z5,z6])],[(0,[z0,z2,z975,z4,z5,z6]),(0,[z54,z2,z924,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z524]),(0,[z0,z2,z976,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z977])],[(0,[z0,z2,z3,z4,z978,z6]),(0,[z404,z0,z2,z4,z66,z6]),(0,[z0,z2,z3,z4,z979,z6]),(0,[z0,z2,z49,z762,z5,z6]),(0,[z0,z2,z3,z980,z5,z6])],[(0,[z505,z2,z71,z4,z5,z6]),(0,[z258,z2,z3,z107,z5,z6]),(0,[z0,z203,z3,z4,z167,z6]),(0,[z0,z2,z981,z4,z5,z6]),(0,[z0,z2,z4,z5,z982,z6]),(0,[z0,z2,z3,z4,z983,z6]),(0,[z0,z3,z813,z8,z5,z6]),(0,[z0,z419,z3,z4,z43,z6]),(0,[z0,z226,z3,z4,z5,z138]),(0,[z0,z85,z2,z3,z78,z6]),(0,[z184,z2,z3,z4,z5,z771])],[(0,[z0,z2,z3,z4,z984,z6])],[(0,[z2,z3,z4,z5,z985,z11]),(0,[z0,z2,z3,z986,z5,z6]),(0,[z0,z241,z3,z4,z646,z6]),(0,[z85,z81,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z987,z6])],[(0,[z60,z85,z2,z3,z4,z6]),(0,[z239,z2,z3,z97,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z988,z6]),(0,[z159,z0,z2,z4,z34,z5]),(0,[z75,z0,z293,z4,z5,z80])],[(0,[z70,z2,z178,z4,z5,z6]),(0,[z0,z989,z2,z3,z4,z6]),(0,[z0,z2,z3,z990,z5,z6]),(0,[z12,z85,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z22,z137]),(0,[z159,z0,z2,z3,z816,z5]),(0,[z991,z2,z3,z4,z5,z6]),(0,[z0,z350,z4,z5,z6,z80]),(0,[z75,z0,z3,z4,z5,z857]),(0,[z0,z2,z4,z755,z66,z6]),(0,[z0,z2,z154,z4,z5,z375])],[(0,[z0,z2,z992,z4,z5,z6]),(0,[z0,z2,z993,z4,z5,z6]),(0,[z0,z2,z3,z4,z204,z471]),(0,[z0,z2,z3,z4,z994,z6])],[(0,[z359,z121,z3,z4,z5,z6]),(0,[z0,z2,z545,z4,z5,z238]),(0,[z0,z2,z125,z4,z5,z471]),(0,[z0,z2,z3,z995,z5,z6]),(0,[z0,z2,z4,z5,z6,z302]),(0,[z23,z0,z3,z813,z5,z6]),(0,[z0,z2,z208,z7,z5,z6]),(0,[z0,z2,z340,z4,z5,z262]),(0,[z0,z2,z3,z4,z996,z6])],[(0,[z0,z997,z2,z3,z4,z6]),(0,[z0,z2,z3,z65,z286,z6]),(0,[z2,z3,z4,z5,z985,z6]),(0,[z158,z0,z41,z4,z5,z6]),(0,[z998,z2,z3,z4,z5,z6]),(0,[z0,z2,z999,z4,z5,z6])],[(0,[z0,z1000,z3,z4,z5,z6]),(0,[z385,z241,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z39,z739])],[(0,[z0,z304,z3,z4,z19,z6]),(0,[z10,z2,z3,z4,z122,z6]),(0,[z0,z2,z3,z4,z5,z1001]),(0,[z0,z2,z3,z4,z1002,z6]),(0,[z0,z2,z3,z4,z5,z985]),(1,[z0,z2,z3,z5,z739])],[(0,[z0,z2,z3,z4,z1003,z6]),(0,[z63,z2,z3,z108,z5,z6]),(1,[z0,z2,z4,z5,z722])]],
   [[(0,[z0,z1004,z3,z4,z5,z6]),(0,[z134,z63,z2,z3,z65,z6]),(0,[z2,z3,z4,z5,z396,z6]),(0,[z0,z2,z397,z4,z19,z6]),(0,[z60,z0,z81,z3,z4,z6]),(0,[z0,z2,z3,z4,z24,z135]),(0,[z0,z2,z1005,z4,z5,z6]),(0,[z0,z1006,z2,z3,z4,z5]),(0,[z82,z0,z2,z154,z78,z6])],[(0,[z52,z2,z3,z4,z5,z137]),(0,[z0,z2,z350,z221,z5,z6]),(0,[z0,z2,z154,z4,z5,z568]),(0,[z0,z2,z1007,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z835])],[(0,[z0,z2,z1008,z4,z5,z6]),(0,[z0,z1009,z3,z4,z5,z6]),(0,[z12,z0,z81,z3,z4,z6]),(0,[z0,z2,z41,z260,z5,z6]),(0,[z1010,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1011,z6])],[(1,[z2,z3,z783,z5,z6]),(0,[z0,z2,z3,z97,z5,z6])],[(0,[z593,z121,z3,z4,z5,z6]),(0,[z10,z123,z3,z4,z206,z6])],[(0,[z184,z2,z3,z4,z117,z6]),(0,[z523,z0,z3,z8,z5,z6]),(0,[z0,z2,z1012,z4,z5,z6]),(1,[z0,z2,z3,z822,z6]),(0,[z1013,z2,z3,z4,z5,z6])],[(0,[z313,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1014,z5,z6]),(0,[z0,z2,z1015,z4,z5,z6]),(0,[z0,z106,z3,z4,z799,z6]),(0,[z0,z226,z350,z4,z5,z6]),(0,[z0,z241,z3,z173,z5,z6]),(0,[z0,z2,z3,z120,z5,z202])],[(0,[z2,z3,z4,z5,z1016,z6]),(0,[z1017,z2,z3,z4,z5,z6]),(0,[z1018,z2,z3,z4,z5,z6])]],
   [[(0,[z198,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z1019,z5,z6]),(0,[z0,z203,z545,z4,z5,z6]),(0,[z0,z2,z1020,z4,z5,z6]),(0,[z258,z2,z3,z783,z5,z6]),(0,[z1021,z2,z3,z4,z5,z6]),(0,[z0,z2,z188,z4,z301,z6])],[(0,[z0,z2,z3,z1022,z5,z6]),(0,[z0,z2,z397,z4,z5,z266]),(0,[z0,z3,z4,z813,z5,z6]),(0,[z0,z2,z3,z177,z5,z80]),(0,[z0,z340,z4,z5,z6,z262])],[(0,[z239,z2,z3,z4,z5,z6]),(0,[z0,z2,z1023,z4,z5,z6]),(0,[z2,z3,z107,z5,z143,z6]),(0,[z159,z0,z2,z4,z5,z262]),(0,[z0,z81,z154,z4,z5,z6]),(0,[z0,z2,z3,z822,z78,z6])],[(0,[z134,z2,z3,z4,z117,z6]),(0,[z0,z2,z1024,z4,z5,z6]),(0,[z75,z0,z350,z4,z5,z80]),(0,[z0,z2,z647,z34,z5,z6]),(0,[z2,z1025,z3,z4,z5,z6]),(0,[z0,z340,z3,z4,z5,z202]),(0,[z82,z0,z242,z3,z78,z6])],[(0,[z134,z0,z2,z3,z78,z6]),(0,[z127,z0,z2,z4,z66,z6])],[(0,[z0,z2,z3,z4,z1026,z6]),(0,[z704,z0,z41,z4,z5,z6]),(0,[z1027,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1028]),(0,[z0,z596,z3,z4,z43,z6]),(0,[z99,z0,z2,z4,z100,z262])],[(1,[z0,z761,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1029]),(0,[z212,z0,z3,z4,z5,z80]),(0,[z0,z2,z208,z355,z5,z6])],[(0,[z0,z2,z3,z4,z1030,z6]),(0,[z0,z2,z3,z4,z5,z1031]),(0,[z0,z2,z397,z4,z5,z6]),(0,[z159,z0,z28,z2,z4,z5]),(0,[z0,z2,z3,z4,z5,z1032]),(0,[z0,z2,z31,z267,z5,z6]),(0,[z0,z2,z3,z4,z5,z1033]),(0,[z0,z2,z3,z5,z822,z6])]],
   [[(0,[z1034,z0,z2,z3,z5,z6]),(0,[z0,z2,z545,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z266]),(0,[z159,z0,z2,z3,z952,z5]),(0,[z0,z3,z4,z799,z19,z6]),(0,[z0,z2,z3,z1035,z4,z5]),(0,[z99,z0,z241,z4,z5,z262]),(0,[z0,z2,z3,z4,z5,z375])],[(0,[z0,z2,z3,z1036,z5,z6]),(0,[z184,z2,z3,z4,z286,z6]),(0,[z366,z3,z4,z8,z5,z6]),(0,[z0,z2,z3,z4,z301,z135])],[(0,[z0,z946,z3,z4,z5,z6]),(0,[z0,z2,z752,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1037,z6]),(0,[z0,z2,z3,z4,z1038,z6]),(0,[z52,z2,z3,z4,z204,z6]),(0,[z1039,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1040]),(1,[z0,z2,z762,z5,z6])],[(0,[z0,z2,z3,z630,z94,z6]),(0,[z0,z2,z3,z4,z1041,z6])],[(0,[z0,z2,z3,z4,z1042,z6]),(0,[z0,z2,z3,z108,z117,z6]),(0,[z60,z2,z3,z4,z213,z6]),(0,[z75,z76,z3,z4,z5,z80]),(0,[z328,z0,z2,z4,z5,z29])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1043,z5,z6]),(0,[z0,z2,z3,z4,z848,z6]),(0,[z0,z2,z3,z4,z5,z1044]),(0,[z1045,z0,z2,z4,z5,z6]),(0,[z0,z2,z170,z4,z5,z202])],[(0,[z2,z71,z924,z4,z5,z6]),(0,[z63,z2,z545,z65,z5,z6]),(0,[z158,z0,z41,z260,z5,z6]),(0,[z0,z2,z3,z4,z5,z1046]),(0,[z366,z2,z3,z4,z5,z72]),(0,[z1047,z2,z3,z4,z5,z6]),(0,[z1048,z2,z3,z4,z5,z6])]],
   [[(0,[z1049,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z24,z6]),(0,[z465,z2,z350,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z857])],[(0,[z63,z2,z3,z51,z65,z6]),(0,[z0,z2,z1050,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z722]),(0,[z0,z2,z3,z4,z1051,z6])],[(0,[z2,z3,z783,z65,z5,z6]),(0,[z0,z2,z3,z221,z5,z6]),(0,[z0,z2,z4,z5,z6,z1052]),(0,[z0,z2,z1053,z4,z5,z6]),(0,[z0,z340,z3,z4,z646,z6])],[(0,[z134,z10,z2,z3,z4,z6]),(0,[z0,z226,z3,z334,z4,z5])],[(0,[z0,z1054,z3,z4,z5,z6]),(0,[z134,z0,z2,z3,z4,z870]),(0,[z258,z2,z3,z484,z5,z6]),(0,[z0,z2,z61,z180,z5,z6]),(0,[z366,z2,z257,z4,z5,z6]),(0,[z0,z421,z3,z267,z5,z6]),(0,[z0,z2,z3,z4,z799,z6]),(0,[z0,z2,z49,z34,z5,z6]),(0,[z0,z2,z3,z4,z1055,z6]),(0,[z85,z2,z3,z4,z78,z6])],[(0,[z63,z2,z3,z65,z5,z6]),(0,[z2,z3,z107,z108,z5,z6]),(0,[z0,z2,z1056,z4,z5,z6]),(0,[z0,z2,z240,z3,z177,z5])],[(0,[z0,z2,z1057,z4,z5,z6]),(0,[z328,z0,z41,z4,z5,z6]),(0,[z0,z2,z3,z1058,z4,z5]),(0,[z1059,z2,z3,z4,z5,z6]),(0,[z328,z0,z2,z4,z5,z39])],[(0,[z168,z2,z3,z4,z5,z6]),(0,[z123,z740,z3,z4,z5,z6]),(0,[z84,z0,z2,z3,z78,z6]),(0,[z0,z3,z4,z799,z5,z6]),(0,[z0,z2,z350,z4,z486,z6]),(0,[z1060,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1061])]],
   [[(0,[z2,z121,z3,z108,z5,z6]),(0,[z0,z2,z3,z4,z5,z1062]),(0,[z0,z1063,z3,z4,z5,z6]),(0,[z0,z2,z3,z1064,z5,z6]),(0,[z0,z2,z782,z4,z5,z6])],[(0,[z99,z0,z2,z350,z4,z5]),(1,[z0,z2,z4,z755,z6]),(0,[z0,z2,z3,z4,z835,z67])],[(0,[z0,z2,z3,z4,z5,z1065]),(0,[z328,z0,z2,z4,z5,z6]),(0,[z0,z2,z1066,z4,z5,z6]),(0,[z0,z2,z1067,z4,z5,z6]),(0,[z0,z2,z1068,z4,z5,z6])],[(0,[z134,z2,z121,z3,z4,z6]),(0,[z0,z197,z3,z4,z122,z6]),(0,[z0,z2,z3,z4,z5,z64]),(0,[z15,z2,z3,z4,z5,z985]),(0,[z0,z2,z595,z4,z129,z6]),(0,[z0,z340,z3,z4,z5,z262])],[(0,[z0,z2,z1069,z4,z5,z6]),(0,[z0,z2,z3,z267,z5,z199]),(0,[z85,z242,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z835,z5])],[(0,[z0,z2,z545,z4,z286,z6]),(0,[z0,z455,z397,z4,z5,z6]),(0,[z239,z2,z3,z260,z5,z6])],[(0,[z0,z2,z3,z4,z1070,z6]),(0,[z0,z2,z3,z4,z5,z1071]),(0,[z0,z203,z279,z4,z5,z6]),(0,[z0,z1072,z3,z4,z5,z6]),(0,[z672,z0,z2,z4,z5,z262]),(0,[z504,z0,z2,z4,z66,z6])],[(0,[z0,z2,z3,z4,z5,z1073]),(0,[z0,z2,z3,z4,z1074,z6]),(0,[z158,z159,z0,z2,z4,z5]),(0,[z313,z2,z3,z4,z646,z6])]],
   [[(0,[z0,z2,z3,z4,z1075,z6]),(0,[z0,z2,z3,z500,z5,z202])],[(0,[z0,z2,z3,z4,z1076,z6]),(0,[z0,z2,z3,z180,z5,z116]),(0,[z158,z239,z41,z4,z5,z6]),(0,[z23,z0,z3,z8,z5,z135]),(0,[z0,z2,z170,z69,z5,z39])],[(0,[z0,z2,z3,z4,z1077,z6]),(0,[z0,z2,z3,z4,z167,z238]),(0,[z63,z2,z3,z65,z5,z64]),(0,[z0,z2,z3,z4,z1078,z6]),(0,[z1079,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1080,z5,z6]),(0,[z0,z340,z240,z4,z5,z6])],[(0,[z82,z0,z2,z3,z108,z6]),(0,[z0,z28,z3,z4,z5,z471]),(0,[z0,z2,z3,z4,z204,z137]),(0,[z0,z2,z3,z4,z822,z6])],[(0,[z0,z2,z33,z4,z336,z6]),(0,[z2,z3,z4,z783,z5,z6]),(0,[z0,z2,z3,z4,z5,z896]),(0,[z2,z3,z108,z5,z117,z6]),(0,[z158,z0,z41,z97,z5,z6]),(0,[z0,z2,z208,z7,z5,z223])],[(0,[z0,z2,z3,z4,z5,z1081]),(0,[z12,z2,z3,z274,z65,z6]),(0,[z2,z3,z4,z848,z117,z6]),(0,[z12,z2,z3,z4,z368,z6]),(0,[z0,z2,z3,z1082,z5,z6])],[(0,[z0,z1083,z3,z4,z5,z6]),(0,[z414,z2,z3,z4,z5,z6]),(0,[z1084,z0,z2,z3,z4,z6]),(0,[z1085,z2,z3,z4,z5,z6])],[(0,[z60,z2,z3,z4,z104,z6]),(0,[z159,z0,z226,z3,z4,z5]),(0,[z0,z2,z69,z3,z5,z602]),(1,[z0,z350,z4,z5,z80]),(0,[z0,z2,z350,z177,z5,z6]),(0,[z99,z0,z2,z4,z5,z722]),(0,[z0,z2,z3,z274,z94,z6]),(1,[z0,z2,z3,z4,z835])]],
   [[(0,[z0,z2,z3,z4,z5,z1086]),(0,[z0,z2,z1087,z4,z5,z6]),(0,[z0,z2,z257,z4,z5,z6]),(0,[z0,z2,z3,z4,z1088,z6]),(0,[z184,z2,z3,z4,z19,z6]),(0,[z754,z2,z3,z4,z5,z6])],[(0,[z465,z2,z3,z4,z5,z6]),(0,[z0,z2,z1089,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z1090,z4,z5,z6]),(0,[z0,z2,z1091,z4,z5,z6]),(0,[z0,z2,z1092,z4,z5,z6])],[(0,[z316,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z97,z5,z471])],[(0,[z1093,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z646,z39])],[(0,[z352,z2,z36,z4,z5,z6]),(0,[z0,z2,z3,z4,z1094,z6]),(0,[z82,z0,z2,z3,z822,z6])],[(0,[z0,z2,z3,z4,z5,z1095]),(0,[z218,z2,z3,z65,z5,z6]),(0,[z0,z1096,z3,z4,z5,z6]),(0,[z15,z2,z3,z4,z5,z11]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z0,z604,z3,z4,z5,z138])],[(0,[z198,z123,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1097]),(0,[z1098,z2,z3,z4,z5,z6]),(0,[z0,z819,z3,z4,z5,z6])],[(0,[z0,z2,z1099,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1100]),(0,[z0,z2,z3,z4,z5,z1101]),(0,[z0,z2,z3,z4,z646,z6]),(0,[z313,z2,z3,z173,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1102]),(0,[z0,z1,z3,z578,z5,z6]),(0,[z0,z2,z3,z4,z286,z64]),(0,[z134,z12,z2,z3,z4,z6]),(0,[z134,z0,z741,z3,z4,z6]),(0,[z0,z2,z3,z4,z486,z6]),(0,[z0,z242,z154,z4,z5,z6])],[(0,[z239,z2,z3,z4,z5,z471]),(0,[z168,z2,z257,z4,z5,z6]),(0,[z0,z2,z1103,z4,z5,z6])],[(0,[z0,z740,z3,z4,z5,z6]),(0,[z0,z2,z3,z107,z286,z6]),(0,[z1104,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1105]),(0,[z168,z2,z3,z4,z24,z6]),(0,[z0,z2,z188,z267,z5,z6]),(0,[z385,z2,z3,z4,z5,z39]),(0,[z0,z2,z240,z4,z5,z29])],[(0,[z0,z2,z3,z4,z5,z1106]),(0,[z1107,z2,z3,z4,z5,z6]),(0,[z0,z2,z1108,z4,z5,z6]),(0,[z0,z2,z1109,z4,z5,z6])],[(0,[z0,z2,z1110,z4,z5,z6]),(0,[z0,z3,z4,z122,z19,z6]),(0,[z0,z2,z3,z463,z5,z202]),(0,[z0,z2,z3,z221,z486,z6]),(0,[z0,z226,z340,z3,z4,z5]),(0,[z99,z0,z2,z4,z5,z262])],[(0,[z525,z121,z3,z4,z5,z6]),(0,[z1111,z2,z3,z4,z5,z6])],[(0,[z60,z2,z3,z4,z155,z6]),(0,[z0,z2,z3,z4,z5,z1112]),(0,[z385,z2,z3,z4,z5,z6]),(0,[z0,z598,z3,z180,z5,z6]),(0,[z0,z2,z61,z4,z5,z266])],[(0,[z0,z2,z3,z4,z167,z6]),(0,[z184,z2,z3,z4,z5,z6]),(0,[z0,z2,z1113,z3,z5,z6]),(0,[z0,z435,z3,z4,z19,z6]),(0,[z76,z2,z350,z4,z5,z6]),(0,[z564,z0,z3,z4,z5,z80]),(0,[z0,z2,z3,z120,z100,z6])]],
   [[(0,[z2,z121,z3,z4,z122,z6]),(0,[z2,z3,z924,z4,z5,z6]),(0,[z0,z2,z3,z108,z19,z6]),(0,[z68,z2,z3,z4,z5,z11]),(0,[z0,z2,z3,z4,z5,z199]),(0,[z0,z1114,z3,z4,z5,z6])],[(0,[z678,z2,z36,z4,z5,z6]),(0,[z99,z0,z2,z4,z5,z471])],[(0,[z159,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z301,z6]),(0,[z0,z2,z257,z4,z5,z135])],[(0,[z0,z2,z3,z4,z1115,z6]),(0,[z0,z2,z279,z4,z286,z6]),(0,[z0,z2,z3,z1116,z5,z6]),(0,[z0,z686,z3,z4,z19,z6]),(0,[z620,z0,z2,z4,z66,z6])],[(0,[z0,z2,z61,z4,z5,z6]),(0,[z0,z2,z3,z94,z822,z6])],[(0,[z637,z123,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z471]),(0,[z1117,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z4,z646,z6])],[(0,[z1118,z0,z2,z4,z5,z6]),(0,[z63,z2,z3,z65,z167,z6]),(0,[z0,z2,z3,z108,z13,z6]),(0,[z159,z0,z3,z4,z5,z80]),(0,[z184,z2,z3,z4,z5,z932])],[(0,[z0,z2,z1119,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z223]),(0,[z0,z2,z3,z762,z5,z6]),(0,[z0,z2,z3,z173,z5,z6]),(0,[z1120,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1121]),(0,[z0,z2,z3,z4,z1122,z6]),(0,[z0,z1123,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1124,z6]),(0,[z0,z2,z397,z108,z5,z6]),(0,[z0,z2,z3,z4,z1125,z5]),(0,[z0,z2,z3,z4,z5,z1126]),(0,[z0,z2,z3,z177,z5,z6]),(0,[z1127,z2,z3,z4,z5,z6]),(0,[z0,z81,z3,z4,z94,z6]),(0,[z0,z1128,z3,z4,z5,z6])],[(0,[z0,z2,z1129,z4,z5,z6]),(0,[z70,z2,z924,z4,z5,z6]),(0,[z0,z2,z3,z108,z5,z266]),(0,[z328,z0,z2,z4,z994,z6]),(0,[z0,z2,z446,z3,z5,z39]),(0,[z85,z2,z3,z4,z94,z6])],[(0,[z1130,z0,z2,z3,z4,z5]),(0,[z0,z2,z397,z4,z5,z116]),(0,[z1131,z2,z3,z4,z5,z6]),(0,[z99,z0,z226,z28,z4,z5])],[(0,[z0,z2,z3,z1132,z5,z6]),(0,[z0,z2,z3,z1133,z5,z6]),(0,[z52,z2,z3,z97,z5,z6]),(0,[z168,z2,z3,z4,z301,z6]),(0,[z1134,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z139,z5,z6])],[(0,[z0,z2,z3,z4,z1135,z6]),(0,[z0,z1136,z3,z4,z5,z6]),(0,[z385,z2,z208,z4,z5,z6]),(0,[z0,z2,z4,z5,z722,z262])],[(0,[z54,z2,z36,z4,z5,z6]),(0,[z0,z2,z1137,z4,z5,z6]),(0,[z0,z2,z1138,z4,z5,z6]),(0,[z0,z581,z3,z4,z19,z6])],[(0,[z10,z123,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1139]),(0,[z85,z2,z154,z4,z5,z6])],[(0,[z573,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z108,z5,z6])]],
   [[(0,[z0,z2,z3,z1140,z5,z6]),(0,[z99,z0,z2,z4,z5,z114])],[(0,[z0,z2,z3,z4,z5,z116]),(0,[z60,z2,z3,z180,z117,z6]),(0,[z0,z226,z3,z4,z5,z586]),(0,[z0,z2,z3,z1141,z5,z6])],[],[(0,[z465,z2,z3,z4,z486,z6])],[(0,[z0,z2,z3,z1142,z5,z6]),(0,[z0,z2,z3,z1143,z5,z6]),(0,[z10,z96,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1144]),(0,[z99,z0,z2,z4,z5,z607])],[(0,[z0,z2,z4,z5,z29,z471]),(0,[z1145,z2,z3,z4,z5,z6]),(0,[z0,z2,z208,z762,z5,z6]),(0,[z0,z2,z208,z4,z5,z223])],[(0,[z134,z0,z2,z3,z274,z6]),(0,[z0,z2,z1146,z4,z5,z6]),(0,[z2,z3,z1147,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1148,z6]),(0,[z258,z203,z3,z4,z5,z6]),(0,[z203,z3,z4,z65,z5,z6]),(0,[z0,z2,z3,z274,z108,z6]),(0,[z158,z0,z53,z41,z4,z5]),(0,[z0,z2,z3,z1149,z4,z5]),(0,[z1150,z2,z3,z4,z5,z6])]],
   [[(0,[z76,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1151,z4,z5]),(0,[z0,z2,z293,z4,z132,z6])],[(0,[z0,z2,z237,z34,z5,z6]),(0,[z0,z2,z3,z1152,z5,z6]),(0,[z0,z2,z41,z4,z5,z471]),(0,[z0,z2,z3,z1153,z5,z6]),(0,[z1154,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z223,z202])],[(0,[z0,z455,z61,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1155]),(0,[z99,z0,z157,z2,z4,z5]),(0,[z0,z2,z3,z1156,z5,z6]),(0,[z23,z0,z3,z8,z5,z6]),(0,[z1157,z2,z3,z4,z5,z6]),(0,[z0,z1158,z3,z4,z5,z6])],[(0,[z2,z3,z65,z5,z286,z6]),(0,[z0,z2,z3,z4,z5,z568])],[(0,[z0,z2,z279,z4,z5,z238]),(0,[z1159,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z274,z610,z6]),(0,[z159,z0,z2,z208,z4,z5]),(0,[z76,z2,z3,z221,z5,z6]),(0,[z0,z2,z170,z120,z5,z6])],[(0,[z0,z2,z3,z4,z1160,z6]),(0,[z27,z2,z3,z4,z5,z11])],[(0,[z52,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1161]),(0,[z2,z3,z65,z117,z78,z6]),(0,[z0,z340,z4,z34,z5,z6])],[(0,[z0,z598,z397,z4,z5,z6]),(0,[z0,z41,z4,z5,z80,z262]),(0,[z0,z2,z1162,z4,z5,z6]),(0,[z385,z2,z3,z4,z646,z6])]],
   [[(0,[z0,z2,z545,z4,z5,z64]),(0,[z0,z598,z3,z4,z5,z266]),(0,[z0,z2,z3,z260,z5,z471]),(0,[z0,z2,z7,z762,z5,z6])],[(0,[z0,z226,z240,z41,z4,z5]),(0,[z75,z465,z3,z4,z5,z80])],[(0,[z765,z2,z3,z4,z5,z6])],[(0,[z0,z407,z3,z4,z286,z6]),(0,[z1163,z2,z3,z4,z5,z6]),(1,[z0,z3,z813,z5,z6]),(0,[z0,z102,z3,z4,z43,z6]),(0,[z465,z2,z3,z177,z5,z6]),(0,[z0,z241,z3,z4,z100,z6])],[(0,[z0,z2,z3,z4,z1164,z6]),(0,[z0,z1165,z3,z4,z5,z6]),(0,[z0,z761,z41,z4,z5,z6]),(0,[z0,z81,z3,z4,z5,z6]),(0,[z1166,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z138,z857]),(0,[z0,z2,z592,z4,z5,z6])],[(1,[z2,z924,z4,z5,z6]),(0,[z85,z2,z3,z4,z5,z6]),(0,[z0,z455,z3,z108,z5,z6]),(0,[z0,z3,z41,z4,z5,z471]),(0,[z159,z1107,z2,z3,z4,z5]),(0,[z0,z2,z3,z1167,z4,z5]),(0,[z1168,z2,z3,z4,z5,z6])],[(0,[z0,z598,z3,z4,z5,z6]),(0,[z0,z2,z31,z8,z5,z6]),(0,[z0,z2,z3,z4,z1169,z6])],[(0,[z0,z1170,z3,z4,z5,z6]),(0,[z0,z455,z3,z4,z5,z116]),(0,[z0,z2,z397,z4,z43,z6]),(0,[z2,z3,z4,z5,z848,z6]),(0,[z319,z0,z2,z3,z78,z6]),(0,[z75,z0,z3,z4,z5,z80]),(0,[z0,z2,z3,z4,z5,z739]),(0,[z0,z42,z2,z3,z4,z165])]],
   [[(0,[z60,z203,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1171]),(0,[z0,z1172,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z43,z266]),(0,[z0,z2,z188,z4,z5,z135]),(0,[z0,z2,z3,z4,z1173,z6]),(0,[z0,z2,z208,z7,z5,z199]),(0,[z0,z2,z3,z173,z646,z6]),(0,[z0,z2,z1174,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1175,z6]),(0,[z0,z2,z3,z4,z5,z857])],[(0,[z239,z2,z3,z4,z5,z137]),(0,[z0,z2,z3,z177,z486,z6]),(0,[z0,z2,z348,z34,z5,z6])],[(0,[z0,z2,z3,z5,z1176,z6]),(0,[z0,z2,z736,z4,z5,z6]),(0,[z0,z2,z350,z4,z132,z6]),(0,[z75,z0,z3,z221,z5,z80]),(0,[z414,z2,z3,z4,z5,z375])],[(0,[z84,z2,z3,z65,z5,z6]),(0,[z2,z3,z1177,z4,z5,z6]),(0,[z0,z2,z33,z4,z755,z6]),(1,[z0,z340,z4,z5,z262])],[(0,[z121,z3,z4,z276,z5,z6]),(0,[z70,z2,z376,z4,z5,z6]),(0,[z0,z2,z3,z1178,z5,z6]),(0,[z0,z88,z3,z4,z19,z6]),(0,[z99,z0,z2,z173,z5,z262]),(0,[z0,z2,z1179,z4,z5,z6]),(0,[z184,z2,z1007,z4,z5,z6])],[(0,[z0,z2,z1180,z4,z5,z6]),(0,[z158,z0,z41,z4,z5,z471]),(0,[z0,z2,z3,z4,z5,z72]),(0,[z0,z2,z31,z4,z5,z6]),(0,[z1181,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z122,z6]),(0,[z63,z2,z3,z783,z5,z6]),(0,[z0,z28,z125,z4,z5,z6]),(0,[z0,z2,z1182,z4,z5,z6]),(0,[z1183,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1184]),(0,[z0,z1185,z3,z4,z5,z6]),(0,[z385,z2,z3,z173,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 534) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 534).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1062).take 82) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1144)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [534, 528, 82] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 88).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 174).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [88, 86, 82] = true :=
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

end PEqualNP.Outside.L_meta_38155

theorem PEqualNP.Outside.L_meta_38155 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4294506664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4294506664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38155.solve