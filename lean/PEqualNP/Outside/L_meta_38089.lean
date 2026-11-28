import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38089

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
  Nat.testBit (4278124264 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x10400208b0224620#64 ++ 0x5082001045811231#64 ++ 0xbba10619f1664e77#64 ++ 0xbddd0830cf8b3273#64 : BitVec 256),
   (0x0080082250285280#64 ++ 0x6004004112814294#64 ++ 0x7772186672b8738f#64 ++ 0x7bbb90c33395c39c#64 : BitVec 256),
   (0x2500608504c08144#64 ++ 0x812803042826040a#64 ++ 0xeeece1878cc183fe#64 ++ 0xf777670c3c660c1f#64 : BitVec 256),
   (0x480701500b01280a#64 ++ 0x0240380a80580940#64 ++ 0xe1ff01f80f01fc1d#64 ++ 0xef0ff80fc0780fe0#64 : BitVec 256),
   (0x8e07b4000fd40013#64 ++ 0x04703da0007ea000#64 ++ 0x1fe7fe000ffe0003#64 ++ 0xe0ff3ff0007ff000#64 : BitVec 256),
   (0xf017dfffe000001c#64 ++ 0x0780beffff000000#64 ++ 0xfff7fffff0000000#64 ++ 0x1fffbfffff800000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x666000060080038e 0x733300003004001c

def z1 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186672b8738f 0x7bbb90c33395c39c

def z2 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f1664e77 0xbddd0830cf8b3273

def z3 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878cc183fe 0xf777670c3c660c1f

def z4 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80f01fc1d 0xef0ff80fc0780fe0

def z5 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x7fe7fe060ffe038f 0xf3ff3ff0307ff01c

def z6 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0000000 0x1fffbfffff800000

def z7 : W := mkw 0x2500608504c08144 0x812803042826040a 0x888ce1818c418070 0x8444670c0c620c03

def z8 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0xefffe1ff8fc1ffff 0xff7fff0ffc7e0fff

def z9 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000ffe0003 0xe0ff3ff0007ff000

def z10 : W := mkw 0x0080000010285280 0x6004000000814294 0x0000000002b8738f 0x600000000015c39c

def z11 : W := mkw 0x3540628db4e2c764 0xd1aa03146da7163b 0xffede79ffde7cfff 0xffff6f3cffef3e7f

def z12 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1e00fe07f0000000 0x10f007f03f800000

def z13 : W := mkw 0x2500608504c08144 0x812803042826040a 0x0e00e00780c003e2 0x107007003c06001f

def z14 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xfffffff80ffffc1f 0xefffffffc07fffe0

def z15 : W := mkw 0x4c0721500fc1280a 0x0260390a807e0940 0xefffe1f80fc1fc1f 0xef7fff0fc07e0fe0

def z16 : W := mkw 0x8200940000140011 0x041004a00000a000 0x10001e00003e0000 0x008000f00001f000

def z17 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e00fe0000fe0002 0x00f007f00007f000

def z18 : W := mkw 0x4007015000000008 0x0200380a80000000 0xe1f701f800000000 0x0f0fb80fc0000000

def z19 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff01fc1d 0xfffffffffff80fe0

def z20 : W := mkw 0x2000408500000004 0x0100020428000000 0xeeece1878c01801c 0xf777670c3c600c00

def z21 : W := mkw 0x10000208a0000000 0x0080001045000000 0x1a000601f0000000 0x10d000300f800000

def z22 : W := mkw 0x0000000010204200 0x4000000000810210 0x1100000070204001 0x0888000003810200

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0xa1a1001801004c15 0xad0d0800c0080260

def z24 : W := mkw 0x10400208a0020420 0x1082001045001021 0x8881061981460c70 0x84440830cc0a3063

def z25 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1a000601f0660262 0x10d000300f833013

def z26 : W := mkw 0x0080000010285280 0x6004000000814294 0x0000000002387001 0x000000000011c380

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0x617200600200700d 0x6b0b900300100380

def z28 : W := mkw 0x0000082240000000 0x0000004112000000 0x7772186670000000 0x1bbb90c333800000

def z29 : W := mkw 0x0500200004c08140 0x802801000026040a 0x000800000cc183fe 0xe000400000660c1f

def z30 : W := mkw 0x2500608504c08144 0x812803042826040a 0x444ce1860c818188 0x4222670c30640c0c

def z31 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x405e01e00e01b008 0x4202f00f00700d80

def z32 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x0113007803007c01 0x08089803c01803e0

def z33 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfff7fffff3007c01 0x1fffbfffff9803e0

def z34 : W := mkw 0x10400208b0224620 0x5082001045811231 0x9a810619f1660e72 0x94d40830cf8b3073

def z35 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe01801f80001fc1c 0x0f00c00fc0000fe0

def z36 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x808d01980d018c10 0x8404680cc0680c60

def z37 : W := mkw 0x0e0020000fd40003 0x00700100007ea000 0x000000000ffe0003 0xe0000000007ff000

def z38 : W := mkw 0x0400200004c00000 0x0020010000260000 0x0e00e00000c00002 0x0070070000060000

def z39 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1fe7fe00033e0001 0x00ff3ff00019f000

def z40 : W := mkw 0xf017dfffe001281c 0x0780beffff000940 0xfffffffff001fc1c 0x1fffffffff800fe0

def z41 : W := mkw 0x10400208b0224620 0x5082001045811231 0xffe1061ff1e64fff 0xffff0830ff8f327f

def z42 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0x11131e7870000000 0x088898f3c3800000

def z43 : W := mkw 0xf097dffff028529c 0x6784beffff814294 0xfff7fffff2b8738f 0x7fffbfffff95c39c

def z44 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x17631e0003be0003 0x60bb18f0001df000

def z45 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ba1060001660003 0xa0dd0830000b3000

def z46 : W := mkw 0x10000208a0000000 0x0080001045000000 0xbba10619f0000000 0x1ddd0830cf800000

def z47 : W := mkw 0x0080082250285280 0x6004004112814294 0x7610186670b8738e 0x1bb080c33385c39c

def z48 : W := mkw 0x2100408500008144 0x810802042800040a 0xe0ec01878c0183fc 0xf707600c3c600c1f

def z49 : W := mkw 0x0080082250285280 0x6004004112814294 0x1112186072387001 0x088890c30391c380

def z50 : W := mkw 0x8a879c225b3c5293 0x64543ce112d9e294 0x11131e60733e7001 0x088898f30399f380

def z51 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000d460000 0x80ff3ff0006a3000

def z52 : W := mkw 0x4007015000000008 0x0200380a80000000 0x0113007800000000 0x08089803c0000000

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x4440000600800188 0x422200003004000c

def z54 : W := mkw 0x10400208b0224620 0x5082001045811231 0x99810619f1664c71 0x8ccc0830cf8b3263

def z55 : W := mkw 0x8e87bc225ffc5293 0x64743de112ffe294 0x7ff7fe667ffe738f 0xfbffbff333fff39c

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0xaba1001981404e77 0xbd5d0800cc0a0273

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x0442180002980000 0x402210c00014c000

def z58 : W := mkw 0x0580200014e8d3c0 0xe02c010000a7469e 0x000800000ef9f3ff 0xe00040000077cf9f

def z59 : W := mkw 0x0000000010204200 0x4000000000810210 0xb3a1001871204e17 0xbd9d0800c3890270

def z60 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1101061871264c01 0x08880830c3893260

def z61 : W := mkw 0x0400200004c00000 0x0020010000260000 0x0ee4e0000cc00002 0xe077270000660000

def z62 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x81ef01980f018c11 0xe40f780cc0780c60

def z63 : W := mkw 0xfe17ffffefd4001f 0x07f0bfffff7ea000 0xfff7fffffffe0003 0xffffbffffffff000

def z64 : W := mkw 0x690741d50b01a94e 0x83483a0ea8580d4a 0xe1ff01ff8f01fffd 0xff0ff80ffc780fff

def z65 : W := mkw 0x8e00b4000fd40013 0x047005a0007ea000 0x1e00fe000ffe0003 0xe0f007f0007ff000

def z66 : W := mkw 0x480701501b216a0a 0x4240380a80d90b50 0xf3ff01f87f21fe1f 0xff9ff80fc3f90ff0

def z67 : W := mkw 0x8e87bc224fdc1093 0x24743de1127ee084 0x4456f8660e983188 0x4222b7c33074c18c

def z68 : W := mkw 0x0040000010224620 0x5002000000811231 0x0000000001664e77 0xa0000000000b3273

def z69 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1ba31e00037e0003 0xa0dd18f0001bf000

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0ec01800c01801c 0xe707600c00600c00

def z71 : W := mkw 0x0080082250285280 0x6004004112814294 0x1712186672b87383 0x18b890c33395c39c

def z72 : W := mkw 0x4000015000012808 0x0200000a80000940 0x0010007800007c00 0x08008003c00003e0

def z73 : W := mkw 0xf417ffffe4c0001c 0x07a0bfffff260000 0xfff7fffffcc00002 0xffffbfffffe60000

def z74 : W := mkw 0x080700000b000002 0x0040380000580000 0x01e700000f000001 0xe00f380000780000

def z75 : W := mkw 0xfe17ffffefd5281f 0x07f0bfffff7ea940 0xfffffffffffffc1f 0xffffffffffffffe0

def z76 : W := mkw 0x0400200004c00000 0x0020010000260000 0xeeece1800cc1801e 0xe777670c00660c00

def z77 : W := mkw 0x258068a754e8d3c4 0xe12c03453aa7469e 0xfffef9e7fef9f3ff 0xfffff7cf3ff7cf9f

def z78 : W := mkw 0x70904bfff028528c 0x6384825fff814294 0xe01001fff000738c 0x1f00800fff80039c

def z79 : W := mkw 0x10c00208b02a56a0 0x70860010458152b5 0xbba10619f3fe7fff 0xfddd0830cf9ff3ff

def z80 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0ee6f8000ed80002 0xe07737c00076c000

def z81 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0x4456f9e600000000 0x0222b7cf30000000

def z82 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0xffefff878fff83ff 0xf7ff7ffc3c7ffc1f

def z83 : W := mkw 0x2000408500000004 0x0100020428000000 0xeee4e18780000000 0x1777270c3c000000

def z84 : W := mkw 0x4087097250285288 0x6204384b92814294 0xf7f719fe72b8738f 0x7fbfb8cff395c39c

def z85 : W := mkw 0x10400208b0224620 0x5082001045811231 0xa8810619f1464e74 0x9d440830cf8a3273

def z86 : W := mkw 0x488709725b297a8a 0x6244384b92d94bd4 0xe1ff01fe7f01ff9d 0xff0ff80ff3f80ffc

def z87 : W := mkw 0x2100408500008144 0x810802042800040a 0xeaa80187804183fe 0xb755400c3c020c1f

def z88 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xffefff800fff801f 0xe7ff7ffc007ffc00

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000001800004c14 0x0d000000c0000260

def z90 : W := mkw 0x0080082250285280 0x6004004112814294 0x733000667020738f 0x3b9980033381039c

def z91 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1f701f803007c01 0x0f0fb80fc01803e0

def z92 : W := mkw 0x480001500b01280a 0x0240000a80580940 0xe01801f80f01fc1d 0xef00c00fc0780fe0

def z93 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeffee1e78ec1f3ff 0xff7ff70f3c760f9f

def z94 : W := mkw 0x088708225b285282 0x6044384112d94294 0x77f718667fb8738f 0xfbbfb8c333fdc39c

def z95 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff200700d 0x7fffbfffff900380

def z96 : W := mkw 0x8007940000000010 0x04003ca000000000 0x1fe7fe0000000000 0x00ff3ff000000000

def z97 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xebff01f98f41fe7f 0xff5ff80fcc7a0ff3

def z98 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1004c15 0xbfffbfffff880260

def z99 : W := mkw 0x58470358bb236e2a 0x52c2381ac5d91b71 0xe1ff01f9ff01fe7d 0xff0ff80fcff80ff3

def z100 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1ee4fe000cfe0002 0xe0f727f00067f000

def z101 : W := mkw 0x8007940000000010 0x04003ca000000000 0x11031e0000000000 0x008818f000000000

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x0162000002000001 0x600b100000100000

def z103 : W := mkw 0xf517ffffe4c0815c 0x87a8bfffff26040a 0xfffffffffcc183fe 0xffffffffffe60c1f

def z104 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xe01001fff0000000 0x1f00800fff800000

def z105 : W := mkw 0x0500200004c08140 0x802801000026040a 0x0000000000c003e2 0x000000000006001f

def z106 : W := mkw 0x8e07b4001ff44213 0x44703da000ffa210 0x3fe7fe007ffe4207 0xf9ff3ff003fff210

def z107 : W := mkw 0x0080082250285280 0x6004004112814294 0x1600180670b80382 0x10b000c03385c01c

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x1762180002b80003 0x60bb10c00015c000

def z109 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe88ce1878c4183fc 0x9744670c3c620c1f

def z110 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0xf1ff1ff80f3ffc1d 0xef8ff8ffc079ffe0

def z111 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1ba10601f1660263 0xb0dd08300f8b3013

def z112 : W := mkw 0x9640b608b4f64631 0x54b205b045a7b231 0xbfa1fe19f1fe4e77 0xbdfd0ff0cf8ff273

def z113 : W := mkw 0x0080082250285280 0x6004004112814294 0x1000180070380000 0x008000c00381c000

def z114 : W := mkw 0x0080082250285280 0x6004004112814294 0x601000667000738c 0x1b0080033380039c

def z115 : W := mkw 0x3000428da0000004 0x018002146d000000 0xffe5e79ff0000000 0x1fff2f3cff800000

def z116 : W := mkw 0xc0179d7240000018 0x0600bceb92000000 0x0012186000000000 0x000090c300000000

def z117 : W := mkw 0x9e47b608bff64633 0x54f23db045ffb231 0x1fe7fe01fffe0263 0xf0ff3ff00ffff013

def z118 : W := mkw 0xf057dffff022463c 0x5782beffff811231 0xfff7fffff0004e74 0x1fffbfffff800273

def z119 : W := mkw 0xa700f48504d48155 0x853807a42826a40a 0x1e00fe0780fe03e2 0x10f007f03c07f01f

def z120 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffeef9878ef983ff 0xf7ff77cc3c77cc1f

def z121 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0x9fe7ff9980000000 0x04ff3ffccc000000

def z122 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0400276 0xbfffbfffff820013

def z123 : W := mkw 0x10400208b0224620 0x5082001045811231 0xa0000019f0004e74 0x1d000000cf800273

def z124 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80e01b008 0x4f0ff80fc0700d80

def z125 : W := mkw 0x0000000010204200 0x4000000000810210 0x3320000070204207 0x3999000003810210

def z126 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0xfff31e7ff3fe7fff 0xffff98f3ff9ff3ff

def z127 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x9997fff9f0000000 0x0cccbfffcf800000

def z128 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1660003 0xbfffbfffff8b3000

def z129 : W := mkw 0x0080082250285280 0x6004004112814294 0xf7fe19e67eb9f39f 0xffbff0cf33f5cf9c

def z130 : W := mkw 0x8a879c225b3c5293 0x64543ce112d9e294 0x77731e6673be738f 0x7bbb98f3339df39c

def z131 : W := mkw 0xef07f5d50fd5a95f 0x87783faea87ead4a 0xffffffff8fffffff 0xfffffffffc7fffff

def z132 : W := mkw 0x0000082240000000 0x0000004112000000 0x1600180670000000 0x10b000c033800000

def z133 : W := mkw 0x30104aafe0000004 0x018082557f000000 0x00000007f0000000 0x100000003f800000

def z134 : W := mkw 0x90479608b0224630 0x54823cb045811231 0xbfe7fe19f1664e77 0xbdff3ff0cf8b3273

def z135 : W := mkw 0xf057dffff022463c 0x5782beffff811231 0xfff7fffff1664e77 0xbfffbfffff8b3273

def z136 : W := mkw 0x0080082250285280 0x6004004112814294 0xfff21867f2f873ff 0xffff90c33f97c39f

def z137 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xa1b3007803007c15 0xad0d9803c01803e0

def z138 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x5fffffe00fffb00b 0xe2ffffff007ffd80

def z139 : W := mkw 0x2500608504c08144 0x812803042826040a 0x444ce1860cc183fe 0xe222670c30660c1f

def z140 : W := mkw 0x3140428db022c764 0xd18a02146d81163b 0xfba9079ff167cfff 0xbfdd483cff8b3e7f

def z141 : W := mkw 0x080000000b012802 0x0040000000580940 0x000800000f01fc1d 0xe000400000780fe0

def z142 : W := mkw 0x488709725b297a8a 0x6244384b92d94bd4 0xf7ff19fe7fb9ff9f 0xffbff8cff3fdcffc

def z143 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe11b01f80301fc1d 0x0f08d80fc0180fe0

def z144 : W := mkw 0xb510feafe4c08154 0x85a887f57f26040a 0xfeecff87fcc183fe 0xf7f767fc3fe60c1f

def z145 : W := mkw 0x258068a754e8d3c4 0xe12c03453aa7469e 0x1e00f807f0f803e2 0x10f007c03f87c01f

def z146 : W := mkw 0x2000408500000004 0x0100020428000000 0x4444e18600000000 0x0222270c30000000

def z147 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0x444ef9860e998188 0x422277cc3074cc0c

def z148 : W := mkw 0xce07b5500fd4001b 0x06703daa807ea000 0xfff7fff80ffe0003 0xefffbfffc07ff000

def z149 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe00801878cc183fe 0xf700400c3c660c1f

def z150 : W := mkw 0xf517ffffe4c0815c 0x87a8bfffff26040a 0xfffffffffc818188 0x5fffffffffe40c0c

def z151 : W := mkw 0x58470358ab032c2a 0x12c2381ac5581961 0x888d07998d478c70 0x8444683ccc6a3c63

def z152 : W := mkw 0x0080082250285280 0x6004004112814294 0x717218607238700d 0x6b8b90c30391c380

def z153 : W := mkw 0x0080082240081080 0x2004004112004084 0x4452186602983188 0x422290c33014c18c

def z154 : W := mkw 0x0040000010224620 0x5002000000811231 0x0000000001264c01 0x0000000000093260

def z155 : W := mkw 0x3540628db4e2c764 0xd1aa03146da7163b 0xfeece787fce783fe 0xf7f7673c3fe73c1f

def z156 : W := mkw 0x9e47b608bff64633 0x54f23db045ffb231 0xbfe7fe19fffe4e77 0xfdff3ff0cffff273

def z157 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x11031e00033e0001 0x008818f00019f000

def z158 : W := mkw 0xfa17dfffeb14001f 0x07d0beffff58a000 0xfff7fffff33e0001 0x1fffbfffff99f000

def z159 : W := mkw 0xf097dffff028529c 0x6784beffff814294 0xfff7fffff2387001 0x1fffbfffff91c380

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0xeaec01818c41827e 0xf757600c0c620c13

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x7772186002b8700f 0x6bbb90c30015c380

def z162 : W := mkw 0xb017deafe0000014 0x0580bef57f000000 0x1fe7fe07f0000000 0x10ff3ff03f800000

def z163 : W := mkw 0x70174bffe000000c 0x0380ba5fff000000 0xe1f701fff0000000 0x1f0fb80fff800000

def z164 : W := mkw 0x0e0720000fd40003 0x00703900007ea000 0x01e700000ffe0003 0xe00f3800007ff000

def z165 : W := mkw 0x10000a2ae0000000 0x0080005157000000 0xfff31e7ff0000000 0x1fff98f3ff800000

def z166 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xfbff07f80f67fc1f 0xefdff83fc07b3fe0

def z167 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfbed0799fd67ce7f 0xffdf683ccfeb3e73

def z168 : W := mkw 0x2100408500008144 0x810802042800040a 0xe0080187800183fc 0x1700400c3c000c1f

def z169 : W := mkw 0xf517f7dda4c0815c 0x87a8bfbeed26040a 0x888de7998c418070 0x84446f3ccc620c03

def z170 : W := mkw 0x080700000b012802 0x0040380000580940 0x01ef00000f01fc1d 0xe00f780000780fe0

def z171 : W := mkw 0x0a0000000b140003 0x005000000058a000 0x00000000033e0001 0x000000000019f000

def z172 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0885e6000d460000 0x80442f30006a3000

def z173 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xe456f9fff0000000 0x1f22b7cfff800000

def z174 : W := mkw 0x8680bc2254fc5291 0x643405e112a7e294 0x7f72fe6672fe738f 0x7bfb97f33397f39c

def z175 : W := mkw 0x0540200014e2c760 0xd02a010000a7163b 0x000800000de7cfff 0xe0004000006f3e7f

def z176 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7ffffff000001 0xffffbffffff80000

def z177 : W := mkw 0x9a479608bb364633 0x54d23cb045d9b231 0x11031e18733e4c01 0x088818f0c399f260

def z178 : W := mkw 0xb510feafe4c08154 0x85a887f57f26040a 0x1e00fe07f0c003e2 0x10f007f03f86001f

def z179 : W := mkw 0xf057dfffe002043c 0x1782beffff001021 0xfff7fffff1460c70 0x9fffbfffff8a3063

def z180 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0xe9f7e7f980000000 0x0f4fbf3fcc000000

def z181 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2b80003 0x7fffbfffff95c000

def z182 : W := mkw 0x0000082240000000 0x0000004112000000 0x6010006670000000 0x1b00800333800000

def z183 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x0400f80000980000 0x002007c00004c000

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0e4018000000000 0x0707200c00000000

def z185 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0x1e001e07f0fe03e2 0x10f000f03f87f01f

def z186 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0x8885e79980000000 0x04442f3ccc000000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x00e400000c000000 0xe007200000600000

def z188 : W := mkw 0xf117dfffe000815c 0x8788beffff00040a 0xfffffffff00183fc 0x1fffffffff800c1f

def z189 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x819f01f80f01fc11 0x8c0cf80fc0780fe0

def z190 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffd018c10 0x9fffffffffe80c60

def z191 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffe01b008 0x5ffffffffff00d80

def z192 : W := mkw 0x0080082250285280 0x6004004112814294 0x6010006672b8738f 0x7b0080033395c39c

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0x3320000070000000 0x1999000003800000

def z194 : W := mkw 0x0000000000000000 0x0000000000000000 0x0112006002007001 0x0808900300100380

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0xaaa0000180400276 0xb55500000c020013

def z196 : W := mkw 0x58070358ab01280a 0x02c0381ac5580940 0xfbff07f9ff01fc1d 0xffdff83fcff80fe0

def z197 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeee4e18780c003e2 0x1777270c3c06001f

def z198 : W := mkw 0x3540628da4c28564 0x91aa03146d26142b 0x888de7998d478c70 0x84446f3ccc6a3c63

def z199 : W := mkw 0x080700000b000002 0x0040380000580000 0x004600000e000000 0x4002300000700000

def z200 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x445ef9e00e99b008 0x4222f7cf0074cd80

def z201 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0xeee5e79f80000000 0x17772f3cfc000000

def z202 : W := mkw 0x58470358bb236e2a 0x52c2381ac5d91b71 0xfbff07f9ff67fe7f 0xffdff83fcffb3ff3

def z203 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0a0000000000014 0xa505000000000000

def z204 : W := mkw 0x10400208b0224620 0x5082001045811231 0x0000001870004c00 0x08000000c3800260

def z205 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x5e56ffe7f0000000 0x12f2b7ff3f800000

def z206 : W := mkw 0x0080000010285280 0x6004000000814294 0x3320000072b8738f 0x799900000395c39c

def z207 : W := mkw 0x0000082240000000 0x0000004112000000 0x7772186672b80003 0x7bbb90c33395c000

def z208 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x415f01f80f01fc09 0x4a0af80fc0780fe0

def z209 : W := mkw 0xe097ddf75028529c 0x6704beefba814294 0x7776f9e672b8738f 0x7bbbb7cf3395c39c

def z210 : W := mkw 0x2100408500008144 0x810802042800040a 0x00000007800003e0 0x100000003c00001f

def z211 : W := mkw 0xc007955000000018 0x06003caa80000000 0xfff7fff800000000 0x0fffbfffc0000000

def z212 : W := mkw 0x2500608514e0c344 0xc128030428a7061a 0xffece187fce1c3ff 0xffff670c3fe70e1f

def z213 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0xe9ffe1f98f41fc7d 0xef4fff0fcc7a0fe3

def z214 : W := mkw 0xce87bd725ffd7a9b 0x66743deb92ffebd4 0xfffffffe7fffff9f 0xfffffffff3fffffc

def z215 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80d018c10 0x8f0ff80fc0680c60

def z216 : W := mkw 0x0080082250285280 0x6004004112814294 0x5652186672b8338a 0x52b290c33395c19c

def z217 : W := mkw 0x71104bffe000814c 0x8388825fff00040a 0xe01801fff00183fc 0x1f00c00fff800c1f

def z218 : W := mkw 0x0080082250285280 0x6004004112814294 0x5552186672b87189 0x4aaa90c33395c38c

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a00060000660002 0x00d0003000033000

def z220 : W := mkw 0x0080082250285280 0x6004004112814294 0x667000667080738e 0x7b3380033384039c

def z221 : W := mkw 0x70504bfff022462c 0x5382825fff811231 0xfbb107fff1664e77 0xbfdd883fff8b3273

def z222 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff080038e 0x7fffbfffff84001c

def z223 : W := mkw 0x088000001b297a82 0x6044000000d94bd4 0x000800000fb9ff9f 0xe0004000007dcffc

def z224 : W := mkw 0xf557fffff4e2c77c 0xd7aabfffffa7163b 0xfffffffffde7cfff 0xffffffffffef3e7f

def z225 : W := mkw 0x78174bffeb01280e 0x03c0ba5fff580940 0xe1ff01ffff01fc1d 0xff0ff80ffff80fe0

def z226 : W := mkw 0xf097dfffe008109c 0x2784beffff004084 0xfff7fffff2983188 0x5fffbfffff94c18c

def z227 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x0001060001060000 0x0000083000083000

def z228 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1e46fe000efe0002 0x40f237f00077f000

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001004c15 0xa000000000080260

def z230 : W := mkw 0x8407b40004c00010 0x04203da000260000 0x1fe7fe000cc00002 0xe0ff3ff000660000

def z231 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0xfe10fffff0000000 0x1ff087ffff800000

def z232 : W := mkw 0x0000000000000000 0x0000000000000000 0x1600180000b80002 0x00b000c00005c000

def z233 : W := mkw 0x9e47b608bff64633 0x54f23db045ffb231 0x1fe7fe187ffe4c03 0xe8ff3ff0c3fff260

def z234 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1fa1fe0001fe0003 0xa0fd0ff0000ff000

def z235 : W := mkw 0x7d4763ddbfe3ef6e 0xd3ea3b1eedff1f7b 0xffffe7ffffe7ffff 0xffffff3fffff3fff

def z236 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffede7878de783ff 0xf7ff6f3c3c6f3c1f

def z237 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe1b901f80101fc1d 0xaf0dc80fc0080fe0

def z238 : W := mkw 0x2500608504c08144 0x812803042826040a 0xefede19f8dc1cfff 0xff7f6f0cfc6e0e7f

def z239 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0x1ff7fe7870000000 0x08ffbff3c3800000

def z240 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x5557fffe70000000 0x0aaabffff3800000

def z241 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe05e01f80e01fc1c 0x4f02f00fc0700fe0

def z242 : W := mkw 0x4000015000012808 0x0200000a80000940 0x8008019800018c10 0x0400400cc0000c60

def z243 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xfbb107fff0000000 0x1fdd883fff800000

def z244 : W := mkw 0x8f07b4000fd48153 0x84783da0007ea40a 0x1feffe000fff83ff 0xe0ff7ff0007ffc1f

def z245 : W := mkw 0x0040000010224620 0x5002000000811231 0xa1a1001801664e77 0xad0d0800c00b3273

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0xe1f3007803007c1d 0xef0f9803c01803e0

def z247 : W := mkw 0x0080082240081080 0x2004004112004084 0x4010006600003188 0x020080033000018c

def z248 : W := mkw 0x0000082240000000 0x0000004112000000 0x1112186070000000 0x088890c303800000

def z249 : W := mkw 0x2100408500008144 0x810802042800040a 0x4008018600018188 0x0200400c30000c0c

def z250 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xf1131ffff0000000 0x1f8898ffff800000

def z251 : W := mkw 0xf0d7dffff02a56bc 0x7786beffff8152b5 0xfff7fffff3fe7fff 0xffffbfffff9ff3ff

def z252 : W := mkw 0x0080082240081080 0x2004004112004084 0x0012186002183000 0x000090c30010c180

def z253 : W := mkw 0x10400208a0020420 0x1082001045001021 0xa9a1061981464c75 0xad4d0830cc0a3263

def z254 : W := mkw 0x0000082250204200 0x4000004112810210 0x7772186670204207 0x3bbb90c333810210

def z255 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0xbba5e799f0000000 0x1ddd2f3ccf800000

def z256 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xe895e7fff0000000 0x1f44af3fff800000

def z257 : W := mkw 0x488701501b297a8a 0x6244380a80d94bd4 0xe1ff01f80fb9ff9f 0xef0ff80fc07dcffc

def z258 : W := mkw 0x0f0020000fd48143 0x80780100007ea40a 0x000800000fff83ff 0xe0004000007ffc1f

def z259 : W := mkw 0x2400608504c00004 0x0120030428260000 0xeee4e1878cc00002 0xf777270c3c660000

def z260 : W := mkw 0x0000000000000000 0x0000000000000000 0x1320000000200003 0x2099000000010000

def z261 : W := mkw 0xe517fdf744c0815c 0x8728bfefba26040a 0x445ef9e60c818188 0x4222f7cf30640c0c

def z262 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186670b80382 0x1bbb90c33385c01c

def z263 : W := mkw 0xf097dffff028529c 0x6784beffff814294 0xfff7fffff0b80382 0x1fffbfffff85c01c

def z264 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0xfbb1067ff1667fff 0xbfdd8833ff8b33ff

def z265 : W := mkw 0x0080082250285280 0x6004004112814294 0x1112186072b8738f 0x688890c30395c39c

def z266 : W := mkw 0x4000015000012808 0x0200000a80000940 0x401801e00001b008 0x0200c00f00000d80

def z267 : W := mkw 0x8007940000000010 0x04003ca000000000 0x1fe7fe0002b80003 0x60ff3ff00015c000

def z268 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1f13fe7ff0000000 0x18f89ff3ff800000

def z269 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x0800e60000460000 0x0040073000023000

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z271 : W := mkw 0x0500200004c08140 0x802801000026040a 0xe0ec01800cc183fe 0xe707600c00660c1f

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x2120000000004005 0x2909000000000200

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ba1060000000000 0x00dd083000000000

def z274 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x1ff7fe780ffe7c03 0xe8ffbff3c07ff3e0

def z275 : W := mkw 0xaf87fca75ffcd3d7 0xe57c3fe53affe69e 0xffffffe7fffff3ff 0xffffffff3fffff9f

def z276 : W := mkw 0x080000000b012802 0x0040000000580940 0x000800000d018c10 0x8000400000680c60

def z277 : W := mkw 0x0080082250285280 0x6004004112814294 0x645218667298738c 0x5b2290c33394c39c

def z278 : W := mkw 0x0600200004d40001 0x003001000026a000 0x0000000000fe0002 0x000000000007f000

def z279 : W := mkw 0x8607b40004d40011 0x04303da00026a000 0x1fe7fe0000fe0002 0x00ff3ff00007f000

def z280 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x808d01980f01fc1d 0xe404680cc0780fe0

def z281 : W := mkw 0x0400200004c00000 0x0020010000260000 0xaee4e0018cc00276 0xf57727000c660013

def z282 : W := mkw 0x080700000b000002 0x0040380000580000 0xa1e700180f004c15 0xed0f3800c0780260

def z283 : W := mkw 0xd0579f7af0224638 0x5682bcfbd7811231 0x11131e7871264c01 0x088898f3c3893260

def z284 : W := mkw 0x2500608504c08144 0x812803042826040a 0xaea0e00780c003f6 0xb57507003c06001f

def z285 : W := mkw 0x10000208a0000000 0x0080001045000000 0xa0000019f0000000 0x1d000000cf800000

def z286 : W := mkw 0x258068a744c891c4 0xa12c03453a26448e 0xeefef9e78ed9b3fe 0xf777f7cf3c76cd9f

def z287 : W := mkw 0x2000408500000004 0x0100020428000000 0x0e00e00780000000 0x107007003c000000

def z288 : W := mkw 0x0040000000020420 0x1002000000001021 0x0000000001460c70 0x80000000000a3063

def z289 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x9fefff980fff8c13 0xe4ff7ffcc07ffc60

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a00000180400262 0x105000000c020013

def z291 : W := mkw 0xc80795500b01281a 0x06403caa80580940 0xfffffff80f01fc1d 0xefffffffc0780fe0

def z292 : W := mkw 0x0000000010204200 0x4000000000810210 0x1200000070200202 0x1090000003810010

def z293 : W := mkw 0x10000208a0000000 0x0080001045000000 0x8881061980000000 0x04440830cc000000

def z294 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbfe31e19f3fe4e77 0xfdff18f0cf9ff273

def z295 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x0001001801000c00 0x00000800c0080060

def z296 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe0ed01980d018c1c 0xe707680cc0680c60

def z297 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0x5fefff860fff818b 0xe2ff7ffc307ffc0c

def z298 : W := mkw 0xb010d68da0000014 0x058086b46d000000 0x0800e60180000000 0x004007300c000000

def z299 : W := mkw 0x10400208b0224620 0x5082001045811231 0xa0000019f1664e77 0xbd000000cf8b3273

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0xbba1060181660277 0xb5dd08300c0b3013

def z301 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878c418070 0x9777670c3c620c03

def z302 : W := mkw 0x0000000010204200 0x4000000000810210 0x2000000070004204 0x1900000003800210

def z303 : W := mkw 0x10400208b0224620 0x5082001045811231 0x3321061871264e07 0x39990830c3893270

def z304 : W := mkw 0x10400208b0224620 0x5082001045811231 0x8881061981664e77 0xa4440830cc0b3273

def z305 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xf77219fff0000000 0x1fbb90cfff800000

def z306 : W := mkw 0x0000000010204200 0x4000000000810210 0x737200607220720f 0x7b9b900303910390

def z307 : W := mkw 0x601049f74000000c 0x0300824fba000000 0x401001e600000000 0x0200800f30000000

def z308 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xe5fff9f80f99fc1d 0xef2fffcfc07ccfe0

def z309 : W := mkw 0xf057dffff022463c 0x5782beffff811231 0xfff7fffff1264c01 0x1fffbfffff893260

def z310 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe44ce1878c8183fc 0x5722670c3c640c1f

def z311 : W := mkw 0x80879c2250285290 0x64043ce112814294 0x7ff7fe6672b8738f 0x7bffbff33395c39c

def z312 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0446f8000e980000 0x402237c00074c000

def z313 : W := mkw 0x0080082240081080 0x2004004112004084 0x7772186672983188 0x5bbb90c33394c18c

def z314 : W := mkw 0x75106bffe4c0814c 0x83a8835fff26040a 0xeefce1fffcc183fe 0xff77e70fffe60c1f

def z315 : W := mkw 0x8e87b4001ffc5293 0x64743da000ffe294 0x1fe7fe000ffe738f 0xe0ff3ff0007ff39c

def z316 : W := mkw 0x58470358bb236e2a 0x52c2381ac5d91b71 0x1113067873267c01 0x08889833c39933e0

def z317 : W := mkw 0x080700000b000002 0x0040380000580000 0xe1ef01800f01801d 0xe70f780c00780c00

def z318 : W := mkw 0x0040000010224620 0x5002000000811231 0xaaa0000181664e77 0xb55500000c0b3273

def z319 : W := mkw 0x0500200004c08140 0x802801000026040a 0x0eece0000cc183fe 0xe077670000660c1f

def z320 : W := mkw 0x2500608504c08144 0x812803042826040a 0x8eece1818cc18072 0xe477670c0c660c03

def z321 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0x445ee1e60e81b188 0x4222f70f30740d8c

def z322 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xfee4ff87f0000000 0x17f727fc3f800000

def z323 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0ee5e6000dc60002 0xe0772f30006e3000

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000002b80003 0x600000000015c000

def z325 : W := mkw 0x0e4020001ff64623 0x5072010000ffb231 0x000000000ffe4e77 0xe0000000007ff273

def z326 : W := mkw 0x3540628db4e2c764 0xd1aa03146da7163b 0xbfa1e61ff1e64ff7 0xbdfd0f30ff8f327f

def z327 : W := mkw 0x2500608504c08144 0x812803042826040a 0xcccce1878cc181f8 0xc666670c3c660c0f

def z328 : W := mkw 0x0080082250285280 0x6004004112814294 0x0010006070007000 0x0800800303800380

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001660003 0xa0000000000b3000

def z330 : W := mkw 0x10400208b0224620 0x5082001045811231 0x00000001f0000260 0x100000000f800013

def z331 : W := mkw 0xf857dffffb236e3e 0x57c2beffffd91b71 0xffffffffff67fe7f 0xfffffffffffb3ff3

def z332 : W := mkw 0x0e8028225ffc5283 0x6074014112ffe294 0x777218667ffe738f 0xfbbb90c333fff39c

def z333 : W := mkw 0x0500200004c08140 0x802801000026040a 0x666800060cc183fe 0xf333400030660c1f

def z334 : W := mkw 0x0040000010224620 0x5002000000811231 0x0000000000004e74 0x0000000000000273

def z335 : W := mkw 0x00c00822502a56a0 0x70060041128152b5 0x7772186673fe7fff 0xfbbb90c3339ff3ff

def z336 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffffc01801c 0xffffffffffe00c00

def z337 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xbfe7fe180ffe4c17 0xedff3ff0c07ff260

def z338 : W := mkw 0x0480282254e85280 0x6024014112a74294 0x7ff6f8667ef8738f 0xfbffb7c333f7c39c

def z339 : W := mkw 0xe097ddf74008109c 0x2704beefba004084 0x4456f9e602983188 0x4222b7cf3014c18c

def z340 : W := mkw 0x610041d50001a94c 0x8308020ea8000d4a 0xe01801ff8001fffc 0x1f00c00ffc000fff

def z341 : W := mkw 0x258068a754e8d3c4 0xe12c03453aa7469e 0x7f72f867f2f873ef 0x7bfb97c33f97c39f

def z342 : W := mkw 0xd0179758a0000018 0x0680bcbac5000000 0x0001061800000000 0x00000830c0000000

def z343 : W := mkw 0x2500608504c08144 0x812803042826040a 0x4e4ce1878cc183ea 0x5272670c3c660c1f

def z344 : W := mkw 0xa010dca740000014 0x050086e53a000000 0x0400f80600000000 0x002007c030000000

def z345 : W := mkw 0x0080082250285280 0x6004004112814294 0x3720180670b84387 0x39b900c03385c21c

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x0881060001460000 0x80440830000a3000

def z347 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe7ff01fe0f81ff9f 0xff3ff80ff07c0ffc

def z348 : W := mkw 0x8680bc2254fc5291 0x643405e112a7e294 0x1e00fe0670fe0382 0x10f007f03387f01c

def z349 : W := mkw 0xfe17ffffefd4001f 0x07f0bfffff7ea000 0xfff7fffffd460000 0x9fffbfffffea3000

def z350 : W := mkw 0x9640b608b4f64631 0x54b205b045a7b231 0x1e00fe01f0fe0262 0x10f007f00f87f013

def z351 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0x9fefff818fff8073 0xe4ff7ffc0c7ffc03

def z352 : W := mkw 0xde47b758bff76e3b 0x56f23dbac5ffbb71 0xfffffff9fffffe7f 0xffffffffcffffff3

def z353 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe8ece1818c41807c 0xe747670c0c620c03

def z354 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x7f72fe67f0000000 0x1bfb97f33f800000

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0x0660000000800002 0x6033000000040000

def z356 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xe9ffe7f80f47fc1d 0xef4fff3fc07a3fe0

def z357 : W := mkw 0x3540628db4e2c764 0xd1aa03146da7163b 0x1e00e607f0e603e2 0x10f007303f87301f

def z358 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000e980000 0x40ff3ff00074c000

def z359 : W := mkw 0x50400358b0236e28 0x5282001ac5811b71 0xe01801f9f001fe7c 0x1f00c00fcf800ff3

def z360 : W := mkw 0x3500628da4c08144 0x81a803146d26040a 0xffede79ffcc183fe 0xffff6f3cffe60c1f

def z361 : W := mkw 0xbe17feafefd40017 0x05f0bff57f7ea000 0x1fe7fe07fffe0003 0xf0ff3ff03ffff000

def z362 : W := mkw 0x488709724b09388a 0x2244384b925849c4 0x445e19e60e99b188 0x4222f0cf3074cd8c

def z363 : W := mkw 0x4007097240000008 0x0200384b92000000 0xf7f719fe70000000 0x1fbfb8cff3800000

def z364 : W := mkw 0x258068a754e8d3c4 0xe12c03453aa7469e 0xeefce1e7fcc1f3fe 0xff77e70f3fe60f9f

def z365 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe0fc01f80c01fc1c 0xef07e00fc0600fe0

def z366 : W := mkw 0xe017d5d50000001c 0x0700beaea8000000 0x0004e18000000000 0x0000270c00000000

def z367 : W := mkw 0x0000000000000000 0x0000000000000000 0xe1ed01980d01cc1d 0xef0f680cc0680e60

def z368 : W := mkw 0xf617ffffe4d4001d 0x07b0bfffff26a000 0xfff7fffff0fe0002 0x1fffbfffff87f000

def z369 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x405e01e00f01fc1d 0xe202f00f00780fe0

def z370 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x888de7980d478c10 0x84446f3cc06a3c60

def z371 : W := mkw 0x0000000010204200 0x4000000000810210 0x0000000000204207 0x2000000000010210

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fe31e0003fe0003 0xe0ff18f0001ff000

def z373 : W := mkw 0x200048a740000004 0x010002453a000000 0xfff6f9e7f0000000 0x1fffb7cf3f800000

def z374 : W := mkw 0x0080000010285280 0x6004000000814294 0x0000000000b80382 0x000000000005c01c

def z375 : W := mkw 0x0080082250285280 0x6004004112814294 0x7ff31e6673fe738f 0xfbff98f3339ff39c

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x01a1000001000001 0xa00d080000080000

def z377 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0cc7fe000fde0000 0xc0663ff0007ef000

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x6172006000000000 0x0b0b900300000000

def z379 : W := mkw 0x90079608a0000010 0x04803cb045000000 0xbfe7fe19f0000000 0x1dff3ff0cf800000

def z380 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe09d01f80d01fc1c 0x8f04e80fc0680fe0

def z381 : W := mkw 0xd0979f7af0285298 0x6684bcfbd7814294 0x77731e7e72b8738f 0x7bbb98f3f395c39c

def z382 : W := mkw 0x0e0020000fd40003 0x00700100007ea000 0x1ba106000ffe0003 0xe0dd0830007ff000

def z383 : W := mkw 0x080000000b012802 0x0040000000580940 0x000800000e01b008 0x4000400000700d80

def z384 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x11e71e000f3e0001 0xe08f38f00079f000

def z385 : W := mkw 0x10400208b0224620 0x5082001045811231 0xba000619f0664e76 0x1dd00030cf833273

def z386 : W := mkw 0x0080000010285280 0x6004000000814294 0x6172006002b8738f 0x6b0b90030015c39c

def z387 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f0004e74 0x1ddd0830cf800273

def z388 : W := mkw 0x8007940000000010 0x04003ca000000000 0x0885e60000000000 0x00442f3000000000

def z389 : W := mkw 0x0080082250285280 0x6004004112814294 0x1600180672b8738f 0x70b000c03395c39c

def z390 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x7ff7fe600ffe700f 0xebffbff3007ff380

def z391 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0x11131e78033e7c01 0x088898f3c019f3e0

def z392 : W := mkw 0x0e8020001ffc5283 0x6074010000ffe294 0x000000000ffe738f 0xe0000000007ff39c

def z393 : W := mkw 0x0580282254e8d3c0 0xe02c014112a7469e 0x777a18667ef9f3ff 0xfbbbd0c333f7cf9f

def z394 : W := mkw 0x8000940000000010 0x040004a000000000 0x1e00fe0000000000 0x00f007f000000000

def z395 : W := mkw 0x0000082240000000 0x0000004112000000 0x777218667200700d 0x7bbb90c333900380

def z396 : W := mkw 0x50100b7ae0000008 0x0280805bd7000000 0x0010007870000000 0x08008003c3800000

def z397 : W := mkw 0x10400208b0224620 0x5082001045811231 0xaaa00019f0404e76 0xbd550000cf820273

def z398 : W := mkw 0x084000001b236e22 0x5042000000d91b71 0x000800000f67fe7f 0xe0004000007b3ff3

def z399 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1e85fe000dfe0002 0x80f42ff0006ff000

def z400 : W := mkw 0x2500608504c08144 0x812803042826040a 0x0400e00600800180 0x002007003004000c

def z401 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xbfa1fe1ff0000000 0x1dfd0ff0ff800000

def z402 : W := mkw 0xfe97fffffffc529f 0x67f4bfffffffe294 0xfff7fffffffe738f 0xffffbffffffff39c

def z403 : W := mkw 0x4d0721500fc1a94a 0x8268390a807e0d4a 0xe1ff01f80fc1ffff 0xef0ff80fc07e0fff

def z404 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0xbbb31e79f37e7e77 0xbddd98f3cf9bf3f3

def z405 : W := mkw 0xb090deaff0285294 0x658486f57f814294 0x7f72fe67f2b8738f 0x7bfb97f33f95c39c

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000060000038c 0x130000003000001c

def z407 : W := mkw 0x0080082250285280 0x6004004112814294 0x711218667238738d 0x1b8890c33391c39c

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x8081001801000c10 0x84040800c0080060

def z409 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0x888de7818d478070 0x84446f3c0c6a3c03

def z410 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe17a01f80201fc1d 0x6f0bd00fc0100fe0

def z411 : W := mkw 0x080000000b012802 0x0040000000580940 0xe0ec01800f01fc1d 0xe707600c00780fe0

def z412 : W := mkw 0x3540628db4e2c764 0xd1aa03146da7163b 0xeeece19ffcc1cffe 0xff77670cffe60e7f

def z413 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f1264c01 0x1ddd0830cf893260

def z414 : W := mkw 0x4007015000012808 0x0200380a80000940 0xe1ff01f80001fc1c 0x0f0ff80fc0000fe0

def z415 : W := mkw 0x0000000010204200 0x4000000000810210 0xbba00001f0604277 0xbddd00000f830213

def z416 : W := mkw 0x10400208b0224620 0x5082001045811231 0x3b200601f0664267 0x39d900300f833213

def z417 : W := mkw 0x10400a2af0224620 0x5082005157811231 0xfff31e7ff1664e77 0xbfff98f3ff8b3273

def z418 : W := mkw 0xf517ffffe4c0815c 0x87a8bfffff26040a 0xfff7fffff0c003e2 0x1fffbfffff86001f

def z419 : W := mkw 0x9a479608bb364633 0x54d23cb045d9b231 0xbba31e19f37e4e77 0xbddd18f0cf9bf273

def z420 : W := mkw 0x0080082250285280 0x6004004112814294 0x0000000670000380 0x100000003380001c

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x7762180602b8038f 0x73bb10c03015c01c

def z422 : W := mkw 0x0080082250285280 0x6004004112814294 0x777218667000738c 0x1bbb90c33380039c

def z423 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xf7ff19f80fb9fc1f 0xefbff8cfc07dcfe0

def z424 : W := mkw 0xa700f48504d48155 0x853807a42826a40a 0xfeecff878cff83fe 0xf7f767fc3c67fc1f

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee0000780c003fe 0xf77700003c06001f

def z426 : W := mkw 0xf897dffffb297a9e 0x67c4beffffd94bd4 0xffffffffffb9ff9f 0xfffffffffffdcffc

def z427 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0xbbb31e79f0000000 0x1ddd98f3cf800000

def z428 : W := mkw 0x484701501b236e2a 0x5242380a80d91b71 0xe1ff01f80f67fe7f 0xef0ff80fc07b3ff3

def z429 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1b010619f1664e63 0x18d80830cf8b3273

def z430 : W := mkw 0x50470358b0224628 0x5282381ac5811231 0xfbf707f9f1664e77 0xbfdfb83fcf8b3273

def z431 : W := mkw 0x10400208b0224620 0x5082001045811231 0xb3200019f0204e77 0x3d990000cf810273

def z432 : W := mkw 0x2f0060850fd48147 0x81780304287ea40a 0xeeece1878fff83ff 0xf777670c3c7ffc1f

def z433 : W := mkw 0x10400208a0020420 0x1082001045001021 0x9ba1061981660c73 0xa4dd0830cc0b3063

def z434 : W := mkw 0x8007940000000010 0x04003ca000000000 0x0446f80000000000 0x002237c000000000

def z435 : W := mkw 0x90109e2ae0000010 0x048084f157000000 0x10001e0070000000 0x008000f003800000

def z436 : W := mkw 0x0080082240081080 0x2004004112004084 0x0400180600980180 0x002000c03004c00c

def z437 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1987fe000f7e0001 0x80cc3ff0007bf000

def z438 : W := mkw 0xff17ffffefd4815f 0x87f8bfffff7ea40a 0xffffffffffff83ff 0xfffffffffffffc1f

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0xa1a1001800000000 0x0d0d0800c0000000

def z440 : W := mkw 0x0080082240081080 0x2004004112004084 0x5772186602b8318b 0x62bb90c33015c18c

def z441 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x000c01800c018000 0x0000600c00600c00

def z442 : W := mkw 0x080000000b012802 0x0040000000580940 0xa1a900180f01fc1d 0xed0d4800c0780fe0

def z443 : W := mkw 0x258068a754e8d3c4 0xe12c03453aa7469e 0x777ef9e67eb9f38f 0x7bbbf7cf33f5cf9c

def z444 : W := mkw 0x2500608504c08144 0x812803042826040a 0x0e08e0078cc183fe 0xf07047003c660c1f

def z445 : W := mkw 0x50070358a0000008 0x0280381ac5000000 0xfbf707f9f0000000 0x1fdfb83fcf800000

def z446 : W := mkw 0x0e0020000fd40003 0x00700100007ea000 0x0ee4e0000ffe0003 0xe0772700007ff000

def z447 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x6173007803007c0d 0x6b0b9803c01803e0

def z448 : W := mkw 0x0080082240081080 0x2004004112004084 0x657218660298718d 0x6b2b90c33014c38c

def z449 : W := mkw 0x10400208b0224620 0x5082001045811231 0xb1010619f1264e75 0x1d880830cf893273

def z450 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x9e85ff9ff0000000 0x14f42ffcff800000

def z451 : W := mkw 0xfe17f7ddafd4001f 0x07f0bfbeed7ea000 0x9fe7ff998ffe0003 0xe4ff3ffccc7ff000

def z452 : W := mkw 0xe817ddf74b01281e 0x0740beefba580940 0x445ef9e60e01b008 0x4222f7cf30700d80

def z453 : W := mkw 0x35c06aaff4ead7e4 0xf1ae03557fa756bf 0xffffffffffffffff 0xffffffffffffffff

def z454 : W := mkw 0x8e87bc225ffc5293 0x64743de112ffe294 0x1ff7fe607ffe7003 0xe8ffbff303fff380

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x0101001801004c01 0x08080800c0080260

def z456 : W := mkw 0x0080082250285280 0x6004004112814294 0xf7f3187e73b87f9f 0xffbf98c3f39dc3fc

def z457 : W := mkw 0x6d8769f75fe9fbce 0xe36c3b4fbaff4fde 0xfffff9fffff9ffff 0xffffffcfffffcfff

def z458 : W := mkw 0x8e87bc225ffc5293 0x64743de112ffe294 0x1fe7fe067ffe0383 0xf0ff3ff033fff01c

def z459 : W := mkw 0x0d0020000fc1a942 0x80680100007e0d4a 0x000800000fc1ffff 0xe0004000007e0fff

def z460 : W := mkw 0x080700000b000002 0x0040380000580000 0x0103000003000001 0x0008180000180000

def z461 : W := mkw 0x10400208b0224620 0x5082001045811231 0xa1a10019f1004e75 0xbd0d0800cf880273

def z462 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0x7776f9e670000000 0x1bbbb7cf33800000

def z463 : W := mkw 0x080700000b000002 0x0040380000580000 0x008500000d000000 0x8004280000680000

def z464 : W := mkw 0x14402208b4e24620 0x50a2011045a71231 0xbfe5e619fde64e77 0xfdff2f30cfef3273

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0xbba1061801664c17 0xaddd0830c00b3260

def z466 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0885e6000ffe0003 0xe0442f30007ff000

def z467 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xbfe7fe018ffe0277 0xf5ff3ff00c7ff013

def z468 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x05e7f8000f980001 0xe02f3fc0007cc000

def z469 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xeef4e1fff0000000 0x1f77a70fff800000

def z470 : W := mkw 0x480709724b01280a 0x0240384b92580940 0xf7ff19fe7f01fc1d 0xffbff8cff3f80fe0

def z471 : W := mkw 0x4e0721500fd5280b 0x0270390a807ea940 0xe1ff01f80ffffc1f 0xef0ff80fc07fffe0

def z472 : W := mkw 0x10000208a0000000 0x0080001045000000 0x1101061870000000 0x08880830c3800000

def z473 : W := mkw 0x0400200004c00000 0x0020010000260000 0x0884e0000c400000 0x8044270000620000

def z474 : W := mkw 0xf517f7dda4c0815c 0x87a8bfbeed26040a 0xeeede79f8cc183fe 0xf7776f3cfc660c1f

def z475 : W := mkw 0x250068a744c08144 0x812803453a26040a 0xfffef9e7fcc183fe 0xfffff7cf3fe60c1f

def z476 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0x5ff7ffe600000000 0x02ffbfff30000000

def z477 : W := mkw 0xee17fdf74fd4001f 0x0770bfefba7ea000 0x5ff7ffe60ffe0003 0xe2ffbfff307ff000

def z478 : W := mkw 0x9ec7be2afffe56b3 0x74f63df157fff2b5 0xfff7fe7ffffe7fff 0xffffbff3fffff3ff

def z479 : W := mkw 0x2000408500000004 0x0100020428000000 0xeee4e1878080038e 0x7777270c3c04001c

def z480 : W := mkw 0x880794000b000012 0x04403ca000580000 0x1fe7fe000f000001 0xe0ff3ff000780000

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000200700d 0x6000000000100380

def z482 : W := mkw 0x080700000b000002 0x0040380000580000 0x17e718000fb80003 0xe0bf38c0007dc000

def z483 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1547fe000fbe0001 0x40aa3ff0007df000

def z484 : W := mkw 0x680741d50b01280e 0x03403a0ea8580940 0xefffe1ff8f01fc1d 0xff7fff0ffc780fe0

def z485 : W := mkw 0x2500608504c08144 0x812803042826040a 0xaaace1818c418276 0xb555670c0c620c13

def z486 : W := mkw 0x58470358bb236e2a 0x52c2381ac5d91b71 0xf1ff07f87f27fc1d 0xef8ff83fc3f93fe0

def z487 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x01f700780f007c01 0xe80fb803c07803e0

def z488 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1101061871664e77 0xa8880830c38b3273

def z489 : W := mkw 0x0080000000081080 0x2004000000004084 0x0000000002983188 0x400000000014c18c

def z490 : W := mkw 0x0000000010204200 0x4000000000810210 0x7760000670a0438f 0x7bbb00003385021c

def z491 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1f03fe0003fe0003 0x00f81ff0001ff000

def z492 : W := mkw 0x8e07b4000fd52813 0x04703da0007ea940 0x1feffe000ffffc1f 0xe0ff7ff0007fffe0

def z493 : W := mkw 0x0000000010204200 0x4000000000810210 0x3762180072b84207 0x79bb10c00395c210

def z494 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1a000601f1664e77 0xb0d000300f8b3273

def z495 : W := mkw 0xa507f48504c08154 0x85283fa42826040a 0xffefff878cc183fe 0xf7ff7ffc3c660c1f

def z496 : W := mkw 0x480701500b00000a 0x0240380a80580000 0xe1f701f80f000001 0xef0fb80fc0780000

def z497 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0xe5f7f9fe00000000 0x0f2fbfcff0000000

def z498 : W := mkw 0x2500608504c08144 0x812803042826040a 0x4eece1860cc1818a 0xe277670c30660c0c

def z499 : W := mkw 0xf057d7dda002043c 0x1782bebeed001021 0x8885e79981460c70 0x84442f3ccc0a3063

def z500 : W := mkw 0x4080097250297a88 0x6204004b92814bd4 0xf77a19fe72b9ff9f 0x7fbbd0cff395cffc

def z501 : W := mkw 0x58470358ab032c2a 0x12c2381ac5581961 0xe9ff07f98f47fc7d 0xef4ff83fcc7a3fe3

def z502 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1766f8000eb80003 0x60bb37c00075c000

def z503 : W := mkw 0x9e47b608bff64633 0x54f23db045ffb231 0xbba5e619fd664e77 0xbddd2f30cfeb3273

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0xaaa0000180000000 0x155500000c000000

def z505 : W := mkw 0x650761d504c0814c 0x83283b0ea826040a 0xefffe1ff8cc183fe 0xff7fff0ffc660c1f

def z506 : W := mkw 0x0400200004c00000 0x0020010000260000 0x1fe5e6000de60003 0xe0ff2f30006f3000

def z507 : W := mkw 0xd0579f7af0224638 0x5682bcfbd7811231 0xbbb31e79f1664e77 0xbddd98f3cf8b3273

def z508 : W := mkw 0x0080082250285280 0x6004004112814294 0x617200667200738d 0x7b0b90033390039c

def z509 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfbf30679f3667e7f 0xffdf9833cf9b33f3

def z510 : W := mkw 0x0500200004c08140 0x802801000026040a 0x000800000c818188 0x4000400000640c0c

def z511 : W := mkw 0x0400200004c00000 0x0020010000260000 0x000000000cc00002 0xe000000000660000

def z512 : W := mkw 0x0080082250285280 0x6004004112814294 0x1772186072b87003 0x68bb90c30395c380

def z513 : W := mkw 0x0e0020000fd52803 0x00700100007ea940 0x000800000ffffc1f 0xe0004000007fffe0

def z514 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f0660262 0x1ddd0830cf833013

def z515 : W := mkw 0x2000408500000004 0x0100020428000000 0x8884e18180000000 0x0444270c0c000000

def z516 : W := mkw 0xf517ffffe4c0815c 0x87a8bfffff26040a 0xfffffffffc418070 0x9fffffffffe20c03

def z517 : W := mkw 0x58470358bb236e2a 0x52c2381ac5d91b71 0xbbad0799fd67ce77 0xbddd683ccfeb3e73

def z518 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x011b00780f01fc1d 0xe808d803c0780fe0

def z519 : W := mkw 0xa007d48500000014 0x05003ea428000000 0xffe7ff8780000000 0x17ff3ffc3c000000

def z520 : W := mkw 0xae07f4850fd40017 0x05703fa4287ea000 0xffe7ff878ffe0003 0xf7ff3ffc3c7ff000

def z521 : W := mkw 0x8007940000000010 0x04003ca000000000 0x1fe7fe0001660003 0xa0ff3ff0000b3000

def z522 : W := mkw 0xb610feafe4d40015 0x05b087f57f26a000 0x1e00fe07f0fe0002 0x10f007f03f87f000

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x8880000180400070 0x844400000c020003

def z524 : W := mkw 0x10000208b0204200 0x4080001045810210 0xbba10619f0204207 0x3ddd0830cf810210

def z525 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x0002180002180000 0x000010c00010c000

def z526 : W := mkw 0xee17fdf74fd4001f 0x0770bfefba7ea000 0x4456f9e60e980000 0x4222b7cf3074c000

def z527 : W := mkw 0x4007015000000008 0x0200380a80000000 0x8085019800000000 0x0404280cc0000000

def z528 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0446f8000ffe0003 0xe02237c0007ff000

def z529 : W := mkw 0xb050deaff0224634 0x558286f57f811231 0xbfa1fe1ff1664e77 0xbdfd0ff0ff8b3273

def z530 : W := mkw 0x0000082240000000 0x0000004112000000 0x4452186600000000 0x022290c330000000

def z531 : W := mkw 0x0080000010285280 0x6004000000814294 0x000000000000738c 0x000000000000039c

def z532 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00801800001801c 0x0700400c00000c00

def z533 : W := mkw 0x2100408500008144 0x810802042800040a 0xeeece187800183fc 0x1777670c3c000c1f

def z534 : W := mkw 0x00c00000102a56a0 0x70060000008152b5 0x0000000003fe7fff 0xe0000000001ff3ff

def z535 : W := mkw 0x10400208a0020420 0x1082001045001021 0xbba10619f1460c70 0x9ddd0830cf8a3063

def z536 : W := mkw 0x2000408500000004 0x0100020428000000 0xeee4e18780400276 0xb777270c3c020013

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x000800000c01801c 0xe000400000600c00

def z538 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0x888de1998d418c70 0x84446f0ccc6a0c63

def z539 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x09e7e6000f460001 0xe04f3f30007a3000

def z540 : W := mkw 0x488709725b297a8a 0x6244384b92d94bd4 0x1113187873387c01 0x088898c3c399c3e0

def z541 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1f62fe0002fe0003 0x60fb17f00017f000

def z542 : W := mkw 0x0080082250285280 0x6004004112814294 0x4452186602b8738f 0x622290c33015c39c

def z543 : W := mkw 0x0080082250285280 0x6004004112814294 0x7660180670b8038e 0x73b300c03385c01c

def z544 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0x7f721e67f2fe73ef 0x7bfb90f33f97f39f

def z545 : W := mkw 0x208048a750285284 0x610402453a814294 0xfff6f9e7f2b8738f 0x7fffb7cf3f95c39c

def z546 : W := mkw 0x2500608504c08144 0x812803042826040a 0x0ee4e0078cc003e2 0xf07727003c66001f

def z547 : W := mkw 0x10400208a0020420 0x1082001045001021 0x0001061801060c00 0x00000830c0083060

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000180000274 0x150000000c000013

def z549 : W := mkw 0xf817d7ddab01281e 0x07c0bebeed580940 0xe9ffe7f98f01fc1d 0xef4fff3fcc780fe0

def z550 : W := mkw 0x9e47b608afd60433 0x14f23db0457eb021 0x9fe7fe198ffe0c73 0xe4ff3ff0cc7ff063

def z551 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xc0df01f80f01bc18 0xc606f80fc0780de0

def z552 : W := mkw 0x3140428db022c764 0xd18a02146d81163b 0xe008019ff001cffc 0x1f00400cff800e7f

def z553 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0xf772187ff2b87fff 0x7fbb90c3ff95c3ff

def z554 : W := mkw 0x10000208a0000000 0x0080001045000000 0xbba10619f1004c15 0xbddd0830cf880260

def z555 : W := mkw 0x0080000010285280 0x6004000000814294 0x1762180002b8738f 0x60bb10c00015c39c

def z556 : W := mkw 0xf057d7ddb022463c 0x5782bebeed811231 0xbba5e799f1664e77 0xbddd2f3ccf8b3273

def z557 : W := mkw 0xe817ddf74b01281e 0x0740beefba580940 0xe5fff9fe0f01fc1d 0xef2fffcff0780fe0

def z558 : W := mkw 0x080000000b012802 0x0040000000580940 0x0000000003007c01 0x00000000001803e0

def z559 : W := mkw 0xd8179f7aeb01281a 0x06c0bcfbd7580940 0x11131e7873007c01 0x088898f3c39803e0

def z560 : W := mkw 0xf097dffff028529c 0x6784beffff814294 0xfff7fffff000738c 0x1fffbfffff80039c

def z561 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0xe010007ff0007ffc 0x1f008003ff8003ff

def z562 : W := mkw 0x2500608504c08144 0x812803042826040a 0x666ce1860c81838e 0x7333670c30640c1c

def z563 : W := mkw 0x3540628db4e2c764 0xd1aa03146da7163b 0xbbade799fd67ce77 0xbddd6f3ccfeb3e73

def z564 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1000060070260000 0x0080003003813000

def z565 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0xeeeef9878ed983fe 0xf77777cc3c76cc1f

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000600800382 0x103000003004001c

def z567 : W := mkw 0x80079c2240000010 0x04003ce112000000 0x7ff7fe6670000000 0x1bffbff333800000

def z568 : W := mkw 0xf597fffff4e8d3dc 0xe7acbfffffa7469e 0xfffffffffef9f3ff 0xfffffffffff7cf9f

def z569 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0xeeede19f8dc18ffe 0xf7776f0cfc6e0c7f

def z570 : W := mkw 0x8e07bc224fd40013 0x04703de1127ea000 0x7ff7fe667ffe0003 0xfbffbff333fff000

def z571 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbaa00601f0660276 0xb5d500300f833013

def z572 : W := mkw 0x0040000010224620 0x5002000000811231 0x0000000000660262 0x0000000000033013

def z573 : W := mkw 0x488709725b297a8a 0x6244384b92d94bd4 0x7773187e73b87f8f 0x7bbb98c3f39dc3fc

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x4052006002003008 0x4202900300100180

def z575 : W := mkw 0x650061d504c1a94c 0x8328030ea8260d4a 0xeefce1ff8cc1fffe 0xff77e70ffc660fff

def z576 : W := mkw 0xb050deaff0224634 0x558286f57f811231 0x1e00fe07f0660262 0x10f007f03f833013

def z577 : W := mkw 0x218048a75028d3c4 0xe10c02453a81469e 0xe01801e7f001f3fc 0x1f00c00f3f800f9f

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x677200660280738f 0x7b3b90033014039c

def z579 : W := mkw 0x2500608504c08144 0x812803042826040a 0xee08e18780c183fe 0x1770470c3c060c1f

def z580 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xa1ad01980d01cc15 0xad0d680cc0680e60

def z581 : W := mkw 0xfd17ffffefc1a95e 0x87e8bfffff7e0d4a 0xffffffffffc1ffff 0xfffffffffffe0fff

def z582 : W := mkw 0x080000000b000002 0x0040000000580000 0x000000000f000001 0xe000000000780000

def z583 : W := mkw 0x088008225b297a82 0x6044004112d94bd4 0x777a18667fb9ff9f 0xfbbbd0c333fdcffc

def z584 : W := mkw 0x488709724b09388a 0x2244384b925849c4 0xe5ff19fe0f99fd9d 0xef2ff8cff07ccfec

def z585 : W := mkw 0x4007015000000008 0x0200380a80000000 0xe1ff01f80c01801c 0xef0ff80fc0600c00

def z586 : W := mkw 0x50400358b0236e28 0x5282001ac5811b71 0xfbb907f9f167fe7f 0xbfddc83fcf8b3ff3

def z587 : W := mkw 0x70104bffe001280c 0x0380825fff000940 0xe01801fff001fc1c 0x1f00c00fff800fe0

def z588 : W := mkw 0x2500608504c08144 0x812803042826040a 0x000ce1800c018000 0x0000670c00600c00

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0x0aa0000000400002 0xa055000000020000

def z590 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0xf1f71ff870000000 0x0f8fb8ffc3800000

def z591 : W := mkw 0xf817d7ddab01281e 0x07c0bebeed580940 0x888de7998d018c10 0x84446f3ccc680c60

def z592 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x617e01e00e01f00d 0x6b0bf00f00700f80

def z593 : W := mkw 0x4007015000000008 0x0200380a80000000 0x405601e000000000 0x0202b00f00000000

def z594 : W := mkw 0x0007000000000000 0x0000380000000000 0x01e7000000000000 0x000f380000000000

def z595 : W := mkw 0x2540608514e2c764 0xd12a030428a7163b 0xeeece1878de7cfff 0xf777670c3c6f3e7f

def z596 : W := mkw 0x080700000b000002 0x0040380000580000 0x1be706000f660003 0xe0df3830007b3000

def z597 : W := mkw 0x0e0020000fd40003 0x00700100007ea000 0x000000000e980000 0x400000000074c000

def z598 : W := mkw 0x4000015000000008 0x0200000a80000000 0xe01001f800000000 0x0f00800fc0000000

def z599 : W := mkw 0x9e47b608afd60433 0x14f23db0457eb021 0x8885e6198d460c70 0x84442f30cc6a3063

def z600 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0004e0000c000000 0x0000270000600000

def z601 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1ba1061871664c03 0xa8dd0830c38b3260

def z602 : W := mkw 0x1e402208bff64623 0x50f2011045ffb231 0xbba10619fffe4e77 0xfddd0830cffff273

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x2220000000000206 0x3111000000000010

def z604 : W := mkw 0x0080082250285280 0x6004004112814294 0x3332186072387207 0x399990c30391c390

def z605 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x41ff01e00f01b009 0xe20ff80f00780d80

def z606 : W := mkw 0x70504bfff022462c 0x5382825fff811231 0xe01001fff0004e74 0x1f00800fff800273

def z607 : W := mkw 0x8e47b4001ff64633 0x54723da000ffb231 0x1fe7fe000ffe4e77 0xe0ff3ff0007ff273

def z608 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0x1fe7fe078ffe03e3 0xf0ff3ff03c7ff01f

def z609 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0xbfa11e1ff1fe4ff7 0xbdfd08f0ff8ff27f

def z610 : W := mkw 0xfe57fffffff6463f 0x57f2bfffffffb231 0xfff7fffffffe4e77 0xffffbffffffff273

def z611 : W := mkw 0x2500608504c08144 0x812803042826040a 0x8e8ce1878cc183f2 0x9474670c3c660c1f

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0xe6ec01860c81839e 0xf737600c30640c1c

def z613 : W := mkw 0x0000082240000000 0x0000004112000000 0x777218667080038e 0x7bbb90c33384001c

def z614 : W := mkw 0x18400208bb236e22 0x50c2001045d91b71 0xbba90619ff67fe7f 0xfddd4830cffb3ff3

def z615 : W := mkw 0x0080082240081080 0x2004004112004084 0x667218660298338e 0x733390c33014c19c

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x1101060001260001 0x0088083000093000

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000400276 0xa000000000020013

def z618 : W := mkw 0x10400208b0224620 0x5082001045811231 0xb1a1061871264c15 0xad8d0830c3893260

def z619 : W := mkw 0x0e0020000fd40003 0x00700100007ea000 0x000000000d460000 0x80000000006a3000

def z620 : W := mkw 0xfe17f7ddafd4001f 0x07f0bfbeed7ea000 0x8885e7998d460000 0x84442f3ccc6a3000

def z621 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0x77731e7e70000000 0x1bbb98f3f3800000

def z622 : W := mkw 0x258068a754e8d3c4 0xe12c03453aa7469e 0xfeecf987fcf983fe 0xf7f767cc3fe7cc1f

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x606000000000000c 0x6303000000000000

def z624 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0x77731e7e73be7f8f 0x7bbb98f3f39df3fc

def z625 : W := mkw 0xda179f7aeb14001b 0x06d0bcfbd758a000 0x11131e78733e0001 0x088898f3c399f000

def z626 : W := mkw 0x2000408500000004 0x0100020428000000 0xe000018780000000 0x1700000c3c000000

def z627 : W := mkw 0x10000208a0000000 0x0080001045000000 0xbba10619f0400276 0xbddd0830cf820013

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x6660000600000000 0x1333000030000000

def z629 : W := mkw 0x080000000b012802 0x0040000000580940 0x617a00600f01fc1d 0xeb0bd00300780fe0

def z630 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186672387001 0x1bbb90c33391c380

def z631 : W := mkw 0x0040000010224620 0x5002000000811231 0x3320000071664e77 0xb9990000038b3273

def z632 : W := mkw 0x3040428db0224624 0x518202146d811231 0xffe5e79ff1664e77 0xbfff2f3cff8b3273

def z633 : W := mkw 0x10400208a0020420 0x1082001045001021 0x0800060180460060 0x004000300c023003

def z634 : W := mkw 0xe517fdf744c0815c 0x8728bfefba26040a 0xeefef9e78cc183fe 0xf777f7cf3c660c1f

def z635 : W := mkw 0x2500608504c08144 0x812803042826040a 0x6e60e00780c003ee 0x737307003c06001f

def z636 : W := mkw 0x0e0020000fd40003 0x00700100007ea000 0x176218000ffe0003 0xe0bb10c0007ff000

def z637 : W := mkw 0x0080000010285280 0x6004000000814294 0x6660000602b8738f 0x733300003015c39c

def z638 : W := mkw 0xd8179f7aeb01281a 0x06c0bcfbd7580940 0xf1ff1ff87f01fc1d 0xef8ff8ffc3f80fe0

def z639 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x0012006002003000 0x0000900300100180

def z640 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe0fe01e00e01b01c 0xe707f00f00700d80

def z641 : W := mkw 0x70904bfff028528c 0x6384825fff814294 0xf77219fff2b8738f 0x7fbb90cfff95c39c

def z642 : W := mkw 0x0400200004c00000 0x0020010000260000 0x1fe6f8000ef80003 0xe0ff37c00077c000

def z643 : W := mkw 0x8e87bc225ffc5293 0x64743de112ffe294 0x7776f8667eb8738f 0x7bbbb7c333f5c39c

def z644 : W := mkw 0x2580608514e8d3c4 0xe12c030428a7469e 0xeeece1878ef9f3ff 0xf777670c3c77cf9f

def z645 : W := mkw 0x2d0760850fc08146 0x81683b04287e040a 0xefefe1878fc183ff 0xf77f7f0c3c7e0c1f

def z646 : W := mkw 0x10400208a0020420 0x1082001045001021 0x8000001980000c70 0x04000000cc000063

def z647 : W := mkw 0x10c00a2af02a56a0 0x70860051578152b5 0x11131e78733e7c01 0x088898f3c399f3e0

def z648 : W := mkw 0x080700000b000002 0x0040380000580000 0x61f700600f00700d 0xeb0fb80300780380

def z649 : W := mkw 0x2500608504c08144 0x812803042826040a 0x888ce1818cc183fe 0xe444670c0c660c1f

def z650 : W := mkw 0x2100408500008144 0x810802042800040a 0xe6680187808183fe 0x7733400c3c040c1f

def z651 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0xeef6f9e780000000 0x1777b7cf3c000000

def z652 : W := mkw 0x2d0060850fc1a946 0x81680304287e0d4a 0xeeece1878fc1ffff 0xf777670c3c7e0fff

def z653 : W := mkw 0x4080097250297a88 0x6204004b92814bd4 0xe01801fe7001ff9c 0x1f00c00ff3800ffc

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x404c01800c018008 0x4202600c00600c00

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x1102180002380001 0x008810c00011c000

def z656 : W := mkw 0x4007015000000008 0x0200380a80000000 0xe1f701f80200700d 0x6f0fb80fc0100380

def z657 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe4ece1860c81819c 0xe727670c30640c0c

def z658 : W := mkw 0x0500200004c08140 0x802801000026040a 0xaaa800018cc183fe 0xf55540000c660c1f

def z659 : W := mkw 0x0080082250285280 0x6004004112814294 0x1762180672b80383 0x70bb10c03395c01c

def z660 : W := mkw 0xf017dffff020421c 0x4780beffff810210 0xfff7fffff0204207 0x3fffbfffff810210

def z661 : W := mkw 0x0100000000008140 0x800800000000040a 0x00080000000183fc 0x0000400000000c1f

def z662 : W := mkw 0x10000208a0000000 0x0080001045000000 0xbba10619f1660003 0xbddd0830cf8b3000

def z663 : W := mkw 0x2500608504c08144 0x812803042826040a 0x0800e00180400060 0x004007000c020003

def z664 : W := mkw 0xbf47f68dbff6c777 0xd5fa3fb46dffb63b 0xffefff9fffffcfff 0xffff7ffcfffffe7f

def z665 : W := mkw 0x488709725b297a8a 0x6244384b92d94bd4 0x777e19e67eb9f38f 0x7bbbf0cf33f5cf9c

def z666 : W := mkw 0xde17bf7aefd4001b 0x06f0bdfbd77ea000 0x1ff7fe787ffe0003 0xe8ffbff3c3fff000

def z667 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xccd7ffff80000000 0x0666bffffc000000

def z668 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1ba5e6000d660003 0xa0dd2f30006b3000

def z669 : W := mkw 0x0000000010204200 0x4000000000810210 0x3ba1060071664207 0xb9dd0830038b3210

def z670 : W := mkw 0xd0979f7af0285298 0x6684bcfbd7814294 0x11131e7872387001 0x088898f3c391c380

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x601000600000700c 0x0b00800300000380

def z672 : W := mkw 0x0500200004c08140 0x802801000026040a 0x000800000c418070 0x8000400000620c03

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ee4e00000000000 0x0077270000000000

def z674 : W := mkw 0x2100408500008144 0x810802042800040a 0x8008018180018070 0x0400400c0c000c03

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x1762180000000000 0x00bb10c000000000

def z676 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x11031e000ffe0003 0xe08818f0007ff000

def z677 : W := mkw 0x488709725b297a8a 0x6244384b92d94bd4 0xf1ff19f87f39fc1d 0xef8ff8cfc3f9cfe0

def z678 : W := mkw 0xaf07f4850fd48157 0x85783fa4287ea40a 0xeeede7878dc783fe 0xf7776f3c3c6e3c1f

def z679 : W := mkw 0x15402208b4e2c760 0xd0aa011045a7163b 0xbba90619fde7cfff 0xfddd4830cfef3e7f

def z680 : W := mkw 0x10400208a0020420 0x1082001045001021 0xaaa1061981460e76 0xb5550830cc0a3073

def z681 : W := mkw 0xb090deaff0285294 0x658486f57f814294 0x1e00fe07f0b80382 0x10f007f03f85c01c

def z682 : W := mkw 0x0000000000012800 0x0000000000000940 0x000800000001fc1c 0x0000400000000fe0

def z683 : W := mkw 0x10800a2af0285280 0x6084005157814294 0xfff31e7ff2b8738f 0x7fff98f3ff95c39c

def z684 : W := mkw 0x0040000010224620 0x5002000000811231 0x1ba1060001664e77 0xa0dd0830000b3273

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x808c01800c018010 0x8404600c00600c00

def z686 : W := mkw 0x58470358bb236e2a 0x52c2381ac5d91b71 0xbbb30679f3667e77 0xbddd9833cf9b33f3

def z687 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0xeefee1e78ec1b3fe 0xf777f70f3c760d9f

def z688 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878c818188 0x5777670c3c640c0c

def z689 : W := mkw 0x9e07b608afd40013 0x04f03db0457ea000 0xbfe7fe19fffe0003 0xfdff3ff0cffff000

def z690 : W := mkw 0x258068a744c891c4 0xa12c03453a26448e 0x445ef9e60e99b188 0x4222f7cf3074cd8c

def z691 : W := mkw 0x8e87bc224fdc1093 0x24743de1127ee084 0x5ff7fe660ffe318b 0xe2ffbff3307ff18c

def z692 : W := mkw 0x3540628da4c28564 0x91aa03146d26142b 0xeeede79f8dc78ffe 0xf7776f3cfc6e3c7f

def z693 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0xe5ffe1fe0f81fd9d 0xef2fff0ff07c0fec

def z694 : W := mkw 0xf057dffff022463c 0x5782beffff811231 0xfff7fffff0660262 0x1fffbfffff833013

def z695 : W := mkw 0x0c0720000fc00002 0x00603900007e0000 0x0fe7e0000fc00003 0xe07f3f00007e0000

def z696 : W := mkw 0x600741d50000000c 0x03003a0ea8000000 0xeff7e1ff80000000 0x1f7fbf0ffc000000

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000080038e 0x600000000004001c

def z698 : W := mkw 0x701043dda000000c 0x0380821eed000000 0x8000019980000000 0x0400000ccc000000

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0xe1fe01e00e01f01d 0xef0ff00f00700f80

def z700 : W := mkw 0xfe17ffffefd4001f 0x07f0bfffff7ea000 0xfff7fffffe980000 0x5fffbffffff4c000

def z701 : W := mkw 0x218048a75028d3c4 0xe10c02453a81469e 0xf77a19e7f2b9f3ff 0x7fbbd0cf3f95cf9f

def z702 : W := mkw 0x0400200004c00000 0x0020010000260000 0x6ee4e0060cc0038e 0xf37727003066001c

def z703 : W := mkw 0x58c70b7afb2b7eaa 0x72c6385bd7d95bf5 0xffff1fffffffffff 0xfffff8ffffffffff

def z704 : W := mkw 0x0400200004c00000 0x0020010000260000 0x0444e0000c800000 0x4022270000640000

def z705 : W := mkw 0x4007015000000008 0x0200380a80000000 0xe1f701f801004c15 0xaf0fb80fc0080260

def z706 : W := mkw 0x18470208bb224622 0x50c2381045d91231 0xbbe70619ff664e77 0xfddf3830cffb3273

def z707 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xf3ff01f80f21fc1f 0xef9ff80fc0790fe0

def z708 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xeef6f9fff0000000 0x1f77b7cfff800000

def z709 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1800fe00007e0000 0x00c007f00003f000

def z710 : W := mkw 0x2500608504c08144 0x812803042826040a 0x888ce1878c4183f0 0x9444670c3c620c1f

def z711 : W := mkw 0x10c00208b02a56a0 0x70860010458152b5 0xfbf30679f3fe7fff 0xffdf9833cf9ff3ff

def z712 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe19f01f80f01fc1d 0x8f0cf80fc0780fe0

def z713 : W := mkw 0x200048a740000004 0x010002453a000000 0xfee4f987f0000000 0x17f727cc3f800000

def z714 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xffefff980fff8c1f 0xe7ff7ffcc07ffc60

def z715 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1f62fe07f2b80003 0x70fb17f03f95c000

def z716 : W := mkw 0x0080082250285280 0x6004004112814294 0xfff3187ff3f87fff 0xffff98c3ff9fc3ff

def z717 : W := mkw 0x2500608504c08144 0x812803042826040a 0x444ce1878c8183e8 0x5222670c3c640c1f

def z718 : W := mkw 0x2700608504d48145 0x813803042826a40a 0xeeece1878cff83fe 0xf777670c3c67fc1f

def z719 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x1fefff800fff8003 0xe0ff7ffc007ffc00

def z720 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0xbfa1fe1801fe4c17 0xadfd0ff0c00ff260

def z721 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1fe7fe000f3e0001 0xe0ff3ff00079f000

def z722 : W := mkw 0x0580200014e8d3c0 0xe02c010000a7469e 0xe1fe01e00ef9f3ff 0xef0ff00f0077cf9f

def z723 : W := mkw 0xfa17dfffeb14001f 0x07d0beffff58a000 0xfff7fffff3be0003 0x7fffbfffff9df000

def z724 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1ee6fe000efe0002 0xe0f737f00077f000

def z725 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0xe810e7fff0000000 0x1f40873fff800000

def z726 : W := mkw 0x8f07b4000fd48153 0x84783da0007ea40a 0x7feffe060fff83ff 0xf3ff7ff0307ffc1f

def z727 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffe01fc1c 0x5ffffffffff00fe0

def z728 : W := mkw 0x00c00822502a56a0 0x70060041128152b5 0x7772186672b87fff 0x7bbb90c33395c3ff

def z729 : W := mkw 0x0e0020001ff44203 0x4070010000ffa210 0x000000000ffe4207 0xe0000000007ff210

def z730 : W := mkw 0x9e47b608bff64633 0x54f23db045ffb231 0xa446f819fe984e74 0x5d2237c0cff4c273

def z731 : W := mkw 0xd517bf7ae4c08158 0x86a8bdfbd726040a 0x111b1e787cc183fe 0xe888d8f3c3e60c1f

def z732 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffd018c1c 0xffffffffffe80c60

def z733 : W := mkw 0xb810deafeb012816 0x05c086f57f580940 0x1e08fe07ff01fc1d 0xf0f047f03ff80fe0

def z734 : W := mkw 0x0080082250285280 0x6004004112814294 0x77731e6673be738f 0x7bbb98f3339df39c

def z735 : W := mkw 0xa010dca740000014 0x050086e53a000000 0x1600f80670000000 0x10b007c033800000

def z736 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xf7ff19fe0fb9ff9f 0xffbff8cff07dcffc

def z737 : W := mkw 0x7e106bffefd4000f 0x03f0835fff7ea000 0xe01001fffffe0003 0xff00800ffffff000

def z738 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e60fe0000fe0002 0x60f307f00007f000

def z739 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbfe10619f1e64e77 0xfdff0830cf8f3273

def z740 : W := mkw 0xf897dfffeb09389e 0x27c4beffff5849c4 0xfffffffffe99b188 0x5ffffffffff4cd8c

def z741 : W := mkw 0x0080082250285280 0x6004004112814294 0x777a18667eb9f39f 0xfbbbd0c333f5cf9c

def z742 : W := mkw 0xb090deafe0081094 0x258486f57f004084 0x1e00fe07f0980180 0x10f007f03f84c00c

def z743 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x1ffffe780ffffc1f 0xe8fffff3c07fffe0

def z744 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff3007c1d 0xffffbfffff9803e0

def z745 : W := mkw 0x488709725b297a8a 0x6244384b92d94bd4 0x968d199e7db98f92 0x94b468ccf3edcc7c

def z746 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x415f01f80f01fc1d 0xea0af80fc0780fe0

def z747 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbb010619f1664e77 0x1dd80830cf8b3273

def z748 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xded7fffff0000000 0x16f6bfffff800000

def z749 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff81ff9f 0xfffffffffffc0ffc

def z750 : W := mkw 0x200048a740000004 0x010002453a000000 0xfffef9e7fe01f01d 0xfffff7cf3ff00f80

def z751 : W := mkw 0x6d0761d50fc1a94e 0x83683b0ea87e0d4a 0x0f13e07f83c07fe3 0x18789f03fc1e03ff

def z752 : W := mkw 0x10c00a2ae00a14a0 0x30860051570050a5 0xccd31e7f83de3df8 0xc66698f3fc1ef1ef

def z753 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x819f01f80f01fc1d 0xec0cf80fc0780fe0

def z754 : W := mkw 0x480001500b01280a 0x0240000a80580940 0xe01801f80e01fc1c 0x4f00c00fc0700fe0

def z755 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1ee4fe07f0000000 0x10f727f03f800000

def z756 : W := mkw 0xab07d4850b148157 0x85583ea42858a40a 0xf10b1f87833f83fd 0x178858fc3c19fc1f

def z757 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xddd7fffff0000000 0x0eeebfffff800000

def z758 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0b80002 0x1fffbfffff85c000

def z759 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff3fe0003 0xffffbfffff9ff000

def z760 : W := mkw 0xf057dfffe002043c 0x1782beffff001021 0xfff7fffff1660c73 0xbfffbfffff8b3063

def z761 : W := mkw 0x3540628db4e2c764 0xd1aa03146da7163b 0x554de79e7da7cd89 0x4aaa6f3cf3ed3e6c

def z762 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe0003fe0003 0x00ff3ff0001ff000

def z763 : W := mkw 0xfa17dfffeb15281f 0x07d0beffff58a940 0xfff7fffff33e7c01 0x1fffbfffff99f3e0

def z764 : W := mkw 0xe057ddf75022463c 0x5702beefba811231 0x4456f9e601664e77 0xa222b7cf300b3273

def z765 : W := mkw 0xf057dfffe002043c 0x1782beffff001021 0xfff7fffff1060c00 0x1fffbfffff883060

def z766 : W := mkw 0xf057dfffe002043c 0x1782beffff001021 0xfff7fffff0460060 0x1fffbfffff823003

def z767 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x7ff7fe600ffe0003 0xebffbff3007ff000

def z768 : W := mkw 0xc600b55004d52819 0x063005aa8026a940 0xfe18fff800fffc1e 0x0ff0c7ffc007ffe0

def z769 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff67fc1f 0xfffffffffffb3fe0

def z770 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xbfe7fe198ffe4e77 0xfdff3ff0cc7ff273

def z771 : W := mkw 0x10c00208b02a56a0 0x70860010458152b5 0xffe1061ff3fe7fff 0xffff0830ff9ff3ff

def z772 : W := mkw 0x2500608504c08144 0x812803042826040a 0xfffef9e78ef9f3ff 0xfffff7cf3c77cf9f

def z773 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba90619fd67ce7f 0xfddd4830cfeb3e73

def z774 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x9fe7fe180ffe0c13 0xe4ff3ff0c07ff060

def z775 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xe9f7e7fff0000000 0x1f4fbf3fff800000

def z776 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878c4183fc 0x9777670c3c620c1f

def z777 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xffffffffff01801d 0xfffffffffff80c00

def z778 : W := mkw 0xde17bf7aefd4001b 0x06f0bdfbd77ea000 0x11131e787ffe0003 0xe88898f3c3fff000

def z779 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe01801f80c01fc1c 0xef00c00fc0600fe0

def z780 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff01bc18 0xdffffffffff80de0

def z781 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x5f57fffff0000000 0x1afabfffff800000

def z782 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1feffe000fff801f 0xe0ff7ff0007ffc00

def z783 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1f87fe000ffe0003 0x80fc3ff0007ff000

def z784 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1e00fe07f0400262 0x10f007f03f820013

def z785 : W := mkw 0x0080082250285280 0x6004004112814294 0x4452186672987188 0x4a2290c33394c38c

def z786 : W := mkw 0x10400208a0020420 0x1082001045001021 0x99810619f1460c70 0x8ccc0830cf8a3063

def z787 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1fa1fe07f1660003 0xb0fd0ff03f8b3000

def z788 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xbfe7fe000ffe0017 0xe5ff3ff0007ff000

def z789 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xf5fffffe7f01fc1d 0xefaffffff3f80fe0

def z790 : W := mkw 0x10400208b0224620 0x5082001045811231 0x19010619f1664c61 0x08c80830cf8b3263

def z791 : W := mkw 0xc8079d724b01281a 0x06403ceb92580940 0xfffffffe7f01fc1d 0xfffffffff3f80fe0

def z792 : W := mkw 0x0080082250285280 0x6004004112814294 0x667218667298738e 0x7b3390c33394c39c

def z793 : W := mkw 0x0080082240081080 0x2004004112004084 0x777218667298338e 0x7bbb90c33394c19c

def z794 : W := mkw 0x0080082250285280 0x6004004112814294 0x777e19e67eb9f38f 0x7bbbf0cf33f5cf9c

def z795 : W := mkw 0x0080082250285280 0x6004004112814294 0x7f721e6672fe738f 0x7bfb90f33397f39c

def z796 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1ea0fe0000fe0002 0xa0f507f00007f000

def z797 : W := mkw 0x0580200014e8d3c0 0xe02c010000a7469e 0x000800000cf983fe 0xe00040000067cc1f

def z798 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x7f76ffe7f0000000 0x1bfbb7ff3f800000

def z799 : W := mkw 0x780743ddab01280e 0x03c03a1eed580940 0xffffe7ffff01fc1d 0xffffff3ffff80fe0

def z800 : W := mkw 0xb017deafe0000014 0x0580bef57f000000 0x1e46fe07f0000000 0x10f237f03f800000

def z801 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0x1997fe7870000000 0x08ccbff3c3800000

def z802 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x1ff7fe600ffe3003 0xe0ffbff3007ff180

def z803 : W := mkw 0x0080082250285280 0x6004004112814294 0x3732186672b87387 0x39b990c33395c39c

def z804 : W := mkw 0x2500608504c08144 0x812803042826040a 0xfeece7878ce783fe 0xf7f7673c3c673c1f

def z805 : W := mkw 0x0080082250285280 0x6004004112814294 0x7112186672b8738f 0x7b8890c33395c39c

def z806 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80f01fc09 0x4f0ff80fc0780fe0

def z807 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffece187fcc183fe 0xffff670c3fe60c1f

def z808 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0xf7ff1ff80fbffc1f 0xefbff8ffc07dffe0

def z809 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xf9fffff9ff01fc1d 0xefcfffffcff80fe0

def z810 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x0400f807f0000000 0x102007c03f800000

def z811 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000ffe4c17 0xe0ff3ff0007ff260

def z812 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xfffffffe0fffff9f 0xfffffffff07ffffc

def z813 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0004c14 0x1fffbfffff800260

def z814 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffefff878fff83ff 0xf7ff7ffc3c7ffc1f

def z815 : W := mkw 0x0e8020001ffc5283 0x6074010000ffe294 0x000000000ffe7003 0xe0000000007ff380

def z816 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1e00fe07f0b80002 0x10f007f03f85c000

def z817 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0xbff7fe79f0000000 0x1dffbff3cf800000

def z818 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x809d01f80d01fc10 0x8c04e80fc0680fe0

def z819 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xf557fffff0000000 0x1faabfffff800000

def z820 : W := mkw 0x0080082250285280 0x6004004112814294 0xf7721867f2b873ff 0x7fbb90c33f95c39f

def z821 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xeef5e7fff0000000 0x1f77af3fff800000

def z822 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1f03fe00033e0001 0x00f81ff00019f000

def z823 : W := mkw 0xf097dfffe008109c 0x2784beffff004084 0xfff7fffff0003188 0x1fffbfffff80018c

def z824 : W := mkw 0xd8179f7aeb01281a 0x06c0bcfbd7580940 0x1ff7fe787f007c01 0xe8ffbff3c3f803e0

def z825 : W := mkw 0x0540200014e2c760 0xd02a010000a7163b 0x0000000000e603e2 0x000000000007301f

def z826 : W := mkw 0x0e8020001ffc5283 0x6074010000ffe294 0x000000000eb8738f 0x600000000075c39c

def z827 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xff13fffff0000000 0x1ff89fffff800000

def z828 : W := mkw 0xb007d68da0000014 0x05803eb46d000000 0xffe7ff9ff0000000 0x1fff3ffcff800000

def z829 : W := mkw 0x70174bffe000000c 0x0380ba5fff000000 0xeff7e1fff0000000 0x1f7fbf0fff800000

def z830 : W := mkw 0x0f4020001ff6c763 0xd07a010000ffb63b 0x000800000fffcfff 0xe0004000007ffe7f

def z831 : W := mkw 0x8e07b4000fd52813 0x04703da0007ea940 0xffefff800ffffc1f 0xe7ff7ffc007fffe0

def z832 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x0800e607f0000000 0x104007303f800000

def z833 : W := mkw 0x3000428da0000004 0x018002146d000000 0x1e00e607f0000000 0x10f007303f800000

def z834 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xbe00fe1ff0000000 0x1df007f0ff800000

def z835 : W := mkw 0x00c00822502a56a0 0x70060041128152b5 0x7772186672fe73ef 0x7bbb90c33397f39f

def z836 : W := mkw 0xe097ddf75028529c 0x6704beefba814294 0x4456f9e602b8738f 0x6222b7cf3015c39c

def z837 : W := mkw 0x2500608504c08144 0x812803042826040a 0x4eece1878cc183ea 0xf277670c3c660c1f

def z838 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xe5f7f9fff0000000 0x1f2fbfcfff800000

def z839 : W := mkw 0x2500608504c08144 0x812803042826040a 0xefede19f8cc183fe 0xff7f6f0cfc660c1f

def z840 : W := mkw 0x31c04aaff02ad7e4 0xf18e02557f8156bf 0xe01801fff001fffc 0x1f00c00fff800fff

def z841 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0800382 0x1fffbfffff84001c

def z842 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe8ece1878c4183fc 0xf747670c3c620c1f

def z843 : W := mkw 0xf097d7ddb028529c 0x6784bebeed814294 0x8885e79982b8738f 0x64442f3ccc15c39c

def z844 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1000001 0xbfffbfffff880000

def z845 : W := mkw 0x0f8020001ffcd3c3 0xe07c010000ffe69e 0x000800000ffff3ff 0xe0004000007fff9f

def z846 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186673b87f9f 0xfbbb90c3339dc3fc

def z847 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe0df01f80f01fc1c 0xcf06f80fc0780fe0

def z848 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7ffffff004c15 0xffffbffffff80260

def z849 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xefffe1f80f01fc1d 0xef7fff0fc0780fe0

def z850 : W := mkw 0x10400208a0020420 0x1082001045001021 0xa8810619f1460c70 0x9d440830cf8a3063

def z851 : W := mkw 0xb817deafeb000016 0x05c0bef57f580000 0x1fe7fe07ff000001 0xf0ff3ff03ff80000

def z852 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1513fe7e70000000 0x08a89ff3f3800000

def z853 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffff001801c 0x1fffffffff800c00

def z854 : W := mkw 0x8f07b4000fd48153 0x84783da0007ea40a 0xffefff800fff83ff 0xe7ff7ffc007ffc1f

def z855 : W := mkw 0x2500608504c08144 0x812803042826040a 0xcecce1878cc183fa 0xd676670c3c660c1f

def z856 : W := mkw 0x0580200014e8d3c0 0xe02c010000a7469e 0x000800000eb9f38f 0x600040000075cf9c

def z857 : W := mkw 0x10400208b0224620 0x5082001045811231 0xb9a10619f1664c75 0xadcd0830cf8b3263

def z858 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xfffffff80fff8c13 0xefffffffc07ffc60

def z859 : W := mkw 0x8047940010224630 0x54023ca000811231 0x1fe7fe0001664e77 0xa0ff3ff0000b3273

def z860 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x5ff7ffe7f0000000 0x12ffbfff3f800000

def z861 : W := mkw 0x2500608504c08144 0x812803042826040a 0x4e4ce1878cc183fe 0xf272670c3c660c1f

def z862 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1404e77 0xbfffbfffff8a0273

def z863 : W := mkw 0x0080082250285280 0x6004004112814294 0x7ff6f86672b8738f 0x7bffb7c33395c39c

def z864 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xf9fffff80f7ffc1d 0xefcfffffc07bffe0

def z865 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffffc41827e 0xffffffffffe20c13

def z866 : W := mkw 0x10400208b0224620 0x5082001045811231 0xb9810619f1664e75 0x9dcc0830cf8b3273

def z867 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xe454e1fff0000000 0x1f22a70fff800000

def z868 : W := mkw 0xb110deafe0008154 0x858886f57f00040a 0x1e00fe07f00003e0 0x10f007f03f80001f

def z869 : W := mkw 0xfa17dfffeb14001f 0x07d0beffff58a000 0xfff7fffff2180000 0x1fffbfffff90c000

def z870 : W := mkw 0x0000000000000000 0x0000000000000000 0xe1ff01f80f01fc1d 0xef0ff80fc0780fe0

def z871 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x4456f9e7f0000000 0x1222b7cf3f800000

def z872 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe66ce1878c8183fe 0x7733670c3c640c1f

def z873 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x9ff7fff9f0000000 0x0cffbfffcf800000

def z874 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfbf30679f1664e77 0xbfdf9833cf8b3273

def z875 : W := mkw 0x200048a740000004 0x010002453a000000 0x7f72f867f0000000 0x1bfb97c33f800000

def z876 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e00fe000cfe0002 0xe0f007f00067f000

def z877 : W := mkw 0x2500608504c08144 0x812803042826040a 0xefeee1878ec183ff 0xf77f770c3c760c1f

def z878 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1913fe79f0000000 0x08c89ff3cf800000

def z879 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1f47fe000ffe0003 0x40fa3ff0007ff000

def z880 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfbe10619f1664e7f 0xffdf0830cf8b3273

def z881 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x7e60fe07f0000000 0x13f307f03f800000

def z882 : W := mkw 0xd0079758a0000018 0x06803cbac5000000 0xfff7fff9f0000000 0x1fffbfffcf800000

def z883 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0xfffffff80f3ffc1d 0xefffffffc079ffe0

def z884 : W := mkw 0x0080082240081080 0x2004004112004084 0x5652186672983188 0x52b290c33394c18c

def z885 : W := mkw 0x2100408500008144 0x810802042800040a 0xeeece1878c0183fc 0xf777670c3c600c1f

def z886 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x81ff01f80f01fc11 0xec0ff80fc0780fe0

def z887 : W := mkw 0x8007940000000010 0x04003ca000000000 0x1fe7fe0003fe0003 0xe0ff3ff0001ff000

def z888 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186672b87189 0x5bbb90c33395c38c

def z889 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe05c01f80c01fc1c 0x4f02e00fc0600fe0

def z890 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000dfe0002 0x80ff3ff0006ff000

def z891 : W := mkw 0x10400208a0020420 0x1082001045001021 0xbba10619f1464c75 0xbddd0830cf8a3263

def z892 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0x7ff7ffe670000000 0x1bffbfff33800000

def z893 : W := mkw 0x8607b40004d40011 0x04303da00026a000 0x1e85fe0000fe0002 0x00f42ff00007f000

def z894 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x8885e79ff0000000 0x14442f3cff800000

def z895 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1800fe01f0000000 0x00c007f00f800000

def z896 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2b8700f 0x7fffbfffff95c380

def z897 : W := mkw 0x10c00208b02a56a0 0x70860010458152b5 0xbba10619f37e7e77 0xbddd0830cf9bf3f3

def z898 : W := mkw 0x10400208b0224620 0x5082001045811231 0xa9a10619f1464e75 0xbd4d0830cf8a3273

def z899 : W := mkw 0xf017dfffe001281c 0x0780beffff000940 0xfffffffff201fc1d 0x7fffffffff900fe0

def z900 : W := mkw 0x10400208b0224620 0x5082001045811231 0x98810619f1660c70 0x84c40830cf8b3063

def z901 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe00ce1878c0183fc 0x1700670c3c600c1f

def z902 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0xffb1fffff0000000 0x1ffd8fffff800000

def z903 : W := mkw 0x75106bffe4c0814c 0x83a8835fff26040a 0xe01801fffcc183fe 0xff00c00fffe60c1f

def z904 : W := mkw 0x30104aafe0000004 0x018082557f000000 0xeee4e187f0000000 0x1777270c3f800000

def z905 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x9e81fe1ff0000000 0x14f40ff0ff800000

def z906 : W := mkw 0x0080082250285280 0x6004004112814294 0x6452186672b8738f 0x7b2290c33395c39c

def z907 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0x6456f9e670000000 0x1b22b7cf33800000

def z908 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x0cc7fe000ffe0003 0xe0663ff0007ff000

def z909 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xe894e1fff0000000 0x1f44a70fff800000

def z910 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0200003 0x3fffbfffff810000

def z911 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x7f72fe67f200700d 0x7bfb97f33f900380

def z912 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeaace1878c4183fe 0xb755670c3c620c1f

def z913 : W := mkw 0xf117dfffe000815c 0x8788beffff00040a 0xfffffffff0018070 0x1fffffffff800c03

def z914 : W := mkw 0x80079c2240000010 0x04003ce112000000 0x1fe7fe0670000000 0x10ff3ff033800000

def z915 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0xe410f9fff0000000 0x1f2087cfff800000

def z916 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1fa1fe0000fe0002 0x00fd0ff00007f000

def z917 : W := mkw 0xf017dfffe001281c 0x0780beffff000940 0xfffffffffc01fc1c 0xffffffffffe00fe0

def z918 : W := mkw 0x0080082250285280 0x6004004112814294 0xf7f3187e72b8738f 0x7fbf98c3f395c39c

def z919 : W := mkw 0x8f07b4000fd5a953 0x84783da0007ead4a 0x1feffe000fffffff 0xe0ff7ff0007fffff

def z920 : W := mkw 0x0540200014e2c760 0xd02a010000a7163b 0x0000000001e64ff7 0xa0000000000f327f

def z921 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000fbe0001 0x40ff3ff0007df000

def z922 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1f01fe0001fe0003 0x00f80ff0000ff000

def z923 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeede7878dc783fe 0xf7776f3c3c6e3c1f

def z924 : W := mkw 0x0e8020001ffd7a83 0x6074010000ffebd4 0x000800000fffff9f 0xe0004000007ffffc

def z925 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xbea0fe07f0000000 0x15f507f03f800000

def z926 : W := mkw 0x0e4020001ff64623 0x5072010000ffb231 0x000000000ffe0263 0xe0000000007ff013

def z927 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f1664c71 0x9ddd0830cf8b3263

def z928 : W := mkw 0x70d04bfff02a56ac 0x7386825fff8152b5 0xe01001fff0007ffc 0x1f00800fff8003ff

def z929 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeffee1e78cc183fe 0xff7ff70f3c660c1f

def z930 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1ba7fe000f7e0003 0xa0dd3ff0007bf000

def z931 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x7e60fe0600fe038e 0x73f307f03007f01c

def z932 : W := mkw 0x0d8020001fe9fbc2 0xe06c010000ff4fde 0x000800000ff9ffff 0xe0004000007fcfff

def z933 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfbff07f9ff67fe7f 0xffdff83fcffb3ff3

def z934 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffffc000000 0xffffbfffffe00000

def z935 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1117fff870000000 0x0888bfffc3800000

def z936 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe4ece1878c8183fc 0xf727670c3c640c1f

def z937 : W := mkw 0x10400208a0020420 0x1082001045001021 0x9a810619f1460c70 0x94d40830cf8a3063

def z938 : W := mkw 0x2500608504c08144 0x812803042826040a 0xefffe1ff8fc1ffff 0xff7fff0ffc7e0fff

def z939 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0x5e10ffe7f0000000 0x12f087ff3f800000

def z940 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0xfff7fff870000000 0x0fffbfffc3800000

def z941 : W := mkw 0x0080082250285280 0x6004004112814294 0x1712186672b8738f 0x78b890c33395c39c

def z942 : W := mkw 0x10400208b0224620 0x5082001045811231 0x99810619f1664e77 0xaccc0830cf8b3273

def z943 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfee5ff9ff0000000 0x17f72ffcff800000

def z944 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000ffe700f 0xe0ff3ff0007ff380

def z945 : W := mkw 0x0580200014e8d3c0 0xe02c010000a7469e 0x0000000002f873ef 0x600000000017c39f

def z946 : W := mkw 0xc607b55004d40019 0x06303daa8026a000 0xfff7fff800fe0002 0x0fffbfffc007f000

def z947 : W := mkw 0x10400208b0224620 0x5082001045811231 0x88810619f1460e70 0x94440830cf8a3073

def z948 : W := mkw 0x10c00208b02a56a0 0x70860010458152b5 0xbba10619f1667fff 0xbddd0830cf8b33ff

def z949 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1f01fe1ff0000000 0x18f80ff0ff800000

def z950 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f1464e74 0x9ddd0830cf8a3273

def z951 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1503fe0003be0001 0x00a81ff0001df000

def z952 : W := mkw 0x30104aafe0000004 0x018082557f000000 0x0e00e007f0000000 0x107007003f800000

def z953 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878ec1f3ff 0xf777670c3c760f9f

def z954 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe018ffe0263 0xf0ff3ff00c7ff013

def z955 : W := mkw 0x00c00822502a56a0 0x70060041128152b5 0xf7f3187e73fe7fff 0xffbf98c3f39ff3ff

def z956 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfbb5e7fff0000000 0x1fddaf3fff800000

def z957 : W := mkw 0xb017deafe0000014 0x0580bef57f000000 0x1f03fe07f0000000 0x10f81ff03f800000

def z958 : W := mkw 0xf117dfffe000815c 0x8788beffff00040a 0xfffffffffc0183fc 0xffffffffffe00c1f

def z959 : W := mkw 0xb050deafe0020434 0x158286f57f001021 0x1e00fe07f0460060 0x10f007f03f823003

def z960 : W := mkw 0xf057d7ddb022463c 0x5782bebeed811231 0x8885e79981664e77 0xa4442f3ccc0b3273

def z961 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x3f20fe07f0000000 0x19f907f03f800000

def z962 : W := mkw 0xce07b5500fd4001b 0x06703daa807ea000 0x1ff7fe780ffe0003 0xe8ffbff3c07ff000

def z963 : W := mkw 0x8200940000140011 0x041004a00000a000 0x1e00fe00003e0000 0x00f007f00001f000

def z964 : W := mkw 0x58470358bb236e2a 0x52c2381ac5d91b71 0x5a5e07e1fe67b26a 0x52d2f03f0ff33d93

def z965 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xe014e1fff0000000 0x1f00a70fff800000

def z966 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff01fc11 0x9ffffffffff80fe0

def z967 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1ee4fe0000fe0002 0x00f727f00007f000

def z968 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe060ffe0383 0xf0ff3ff0307ff01c

def z969 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80f01fc11 0x8f0ff80fc0780fe0

def z970 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffede79f8de7cfff 0xffff6f3cfc6f3e7f

def z971 : W := mkw 0x10400208b0224620 0x5082001045811231 0xffed079ffde7cfff 0xffff683cffef3e7f

def z972 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece19f8cc1cffe 0xff77670cfc660e7f

def z973 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xc0df01f80f01fc1d 0xe606f80fc0780fe0

def z974 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0xbea0fe0180fe0276 0xb5f507f00c07f013

def z975 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffece1878ce183ff 0xf7ff670c3c670c1f

def z976 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe01c01f80c01fc1c 0x0f00e00fc0600fe0

def z977 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe9ff01f98f41fc7d 0xef4ff80fcc7a0fe3

def z978 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0xfff6f9e7f0000000 0x1fffb7cf3f800000

def z979 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80f41fe7f 0xef0ff80fc07a0ff3

def z980 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1664c17 0xbfffbfffff8b3260

def z981 : W := mkw 0x8e00b4000fd52813 0x047005a0007ea940 0x1e08fe000ffffc1f 0xe0f047f0007fffe0

def z982 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xfffffff80fffb00b 0xefffffffc07ffd80

def z983 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2980000 0x5fffbfffff94c000

def z984 : W := mkw 0x10400208b0224620 0x5082001045811231 0x9ba10619f1664c73 0xacdd0830cf8b3263

def z985 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1547fe000ffe0003 0xe0aa3ff0007ff000

def z986 : W := mkw 0xf057dfffe002043c 0x1782beffff001021 0xfff7fffff0000c70 0x1fffbfffff800063

def z987 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeefce1e78cc1f3fe 0xff77e70f3c660f9f

def z988 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xffefff980fffcc1f 0xefff7ffcc07ffe60

def z989 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xfbff07f80f01fc1d 0xefdff83fc0780fe0

def z990 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe5ff19f80f99fc1d 0xef2ff8cfc07ccfe0

def z991 : W := mkw 0xb090deafe0081094 0x258486f57f004084 0x5e52fe67f2983188 0x52f297f33f94c18c

def z992 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e81fe0001fe0002 0x80f40ff0000ff000

def z993 : W := mkw 0x98079608ab000012 0x04c03cb045580000 0xbfe7fe19ff004c15 0xfdff3ff0cff80260

def z994 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff280738f 0x7fffbfffff94039c

def z995 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000efe0002 0x40ff3ff00077f000

def z996 : W := mkw 0x00c00822502a56a0 0x70060041128152b5 0xfff21867f3fe7fff 0xffff90c33f9ff3ff

def z997 : W := mkw 0xf097dfffe008109c 0x2784beffff004084 0xfff7fffff298338e 0x7fffbfffff94c19c

def z998 : W := mkw 0x78174bffeb01280e 0x03c0ba5fff580940 0xefffe1ffff01fc1d 0xff7fff0ffff80fe0

def z999 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1fe5fe000dfe0003 0xe0ff2ff0006ff000

def z1000 : W := mkw 0x90079608a0000010 0x04803cb045000000 0x1fe7fe01f0000000 0x10ff3ff00f800000

def z1001 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f3fe4e77 0xfddd0830cf9ff273

def z1002 : W := mkw 0xfa17dfffeb14001f 0x07d0beffff58a000 0xfff7ffffff3e0001 0xffffbffffff9f000

def z1003 : W := mkw 0xf897dfffeb09389e 0x27c4beffff5849c4 0xffffffffff99fd9d 0xfffffffffffccfec

def z1004 : W := mkw 0x10400208b0224620 0x5082001045811231 0xa8810619f1664e77 0xbd440830cf8b3273

def z1005 : W := mkw 0x0e0028224fd40003 0x00700141127ea000 0x777218667ffe0003 0xfbbb90c333fff000

def z1006 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x5ffffff80ffffc0b 0xeaffffffc07fffe0

def z1007 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2b8038f 0x7fffbfffff95c01c

def z1008 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xbfa5ff9ff0000000 0x1dfd2ffcff800000

def z1009 : W := mkw 0x4d8721501fe9fbca 0xe26c390a80ff4fde 0xe1ff01f80ff9ffff 0xef0ff80fc07fcfff

def z1010 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xfff7fff80ffe7c03 0xefffbfffc07ff3e0

def z1011 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x7f72fe6002fe700f 0x6bfb97f30017f380

def z1012 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x41ff01f80f01fc09 0xea0ff80fc0780fe0

def z1013 : W := mkw 0x0080082240081080 0x2004004112004084 0x777218667298718d 0x7bbb90c33394c38c

def z1014 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0xfbf7e7f9f0000000 0x1fdfbf3fcf800000

def z1015 : W := mkw 0x2500608504c08144 0x812803042826040a 0xaeace1878cc183f6 0xb575670c3c660c1f

def z1016 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1fa1fe07f0000000 0x10fd0ff03f800000

def z1017 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x7fffffe00ffff00f 0xebffffff007fff80

def z1018 : W := mkw 0x0e8720001ffc5283 0x6074390000ffe294 0x61f700600ffe738f 0xeb0fb803007ff39c

def z1019 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x15e7fe000fbe0001 0xe0af3ff0007df000

def z1020 : W := mkw 0x0080082250285280 0x6004004112814294 0x7ff2186672f8738f 0xfbff90c33397c39c

def z1021 : W := mkw 0x0080082250285280 0x6004004112814294 0x1772186672b87383 0x78bb90c33395c39c

def z1022 : W := mkw 0x80009c2240000010 0x040004e112000000 0x7f72fe6670000000 0x1bfb97f333800000

def z1023 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1987fe000ffe0003 0xe0cc3ff0007ff000

def z1024 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xfff6ffe7f0000000 0x1fffb7ff3f800000

def z1025 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x9fefff980ffffc1f 0xe4ff7ffcc07fffe0

def z1026 : W := mkw 0xf057dfffe002043c 0x1782beffff001021 0xfff7fffff1464c75 0xbfffbfffff8a3263

def z1027 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xebff01f80f41fc1f 0xef5ff80fc07a0fe0

def z1028 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1e00fe07f0800382 0x10f007f03f84001c

def z1029 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0x5e5effe7fe01b008 0x52f2f7ff3ff00d80

def z1030 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xbfe7fe018ffe0003 0xf5ff3ff00c7ff000

def z1031 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f1664e63 0x1ddd0830cf8b3273

def z1032 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffff301fc1d 0x1fffffffff980fe0

def z1033 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xfbff07f98f67fe7f 0xffdff83fcc7b3ff3

def z1034 : W := mkw 0x0080082250285280 0x6004004112814294 0xfff31e7e73fe7f9f 0xffff98f3f39ff3fc

def z1035 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff41fe7f 0xfffffffffffa0ff3

def z1036 : W := mkw 0xc0079d7240000018 0x06003ceb92000000 0xfff7fffe70000000 0x1fffbffff3800000

def z1037 : W := mkw 0x90009608a0000010 0x048004b045000000 0xbfa1fe19f0000000 0x1dfd0ff0cf800000

def z1038 : W := mkw 0x2000408500000004 0x0100020428000000 0xffe4e187f0000000 0x1fff270c3f800000

def z1039 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1e04ff87f0000000 0x10f027fc3f800000

def z1040 : W := mkw 0x0e4020001ff76e23 0x5072010000ffbb71 0x000800000ffffe7f 0xe0004000007ffff3

def z1041 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f1e64fff 0xfddd0830cf8f327f

def z1042 : W := mkw 0x0080082250285280 0x6004004112814294 0x5772186672b8718b 0x6abb90c33395c38c

def z1043 : W := mkw 0xf117dfffe000815c 0x8788beffff00040a 0xfffffffff0018188 0x1fffffffff800c0c

def z1044 : W := mkw 0x8607b40004d40011 0x04303da00026a000 0x1fe7fe0001fe0003 0xa0ff3ff0000ff000

def z1045 : W := mkw 0x10400208b0224620 0x5082001045811231 0xba810619f1664e76 0x9dd40830cf8b3273

def z1046 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xf1ff07f80f27fc1d 0xef8ff83fc0793fe0

def z1047 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe17e01f80e01fc1d 0x6f0bf00fc0700fe0

def z1048 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbfe31e19f1664e77 0xbdff18f0cf8b3273

def z1049 : W := mkw 0x90179e2ae0000010 0x0480bcf157000000 0x1fe7fe0070000000 0x00ff3ff003800000

def z1050 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xffe7ff800ffe0003 0xe7ff3ffc007ff000

def z1051 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80d01fc1c 0x8f0ff80fc0680fe0

def z1052 : W := mkw 0x0580200014e8d3c0 0xe02c010000a7469e 0x0000000000f803e2 0x000000000007c01f

def z1053 : W := mkw 0x8087940010285290 0x64043ca000814294 0x1fe7fe0002b8738f 0x60ff3ff00015c39c

def z1054 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xc1df01f80f01fc19 0xce0ef80fc0780fe0

def z1055 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7fffffd000000 0x9fffbfffffe80000

def z1056 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e00fe0180fe0262 0x10f007f00c07f013

def z1057 : W := mkw 0xf857dfffeb032c3e 0x17c2beffff581961 0xfffffffffd478c70 0x9fffffffffea3c63

def z1058 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1547fe00033e0001 0x00aa3ff00019f000

def z1059 : W := mkw 0x0080082240081080 0x2004004112004084 0x6452186672983188 0x5b2290c33394c18c

def z1060 : W := mkw 0x4d4721501fe3ef6a 0xd26a390a80ff1f7b 0xe1ff01f80fe7ffff 0xef0ff80fc07f3fff

def z1061 : W := mkw 0x90009608a0000010 0x048004b045000000 0x1e00fe01f0000000 0x10f007f00f800000

def z1062 : W := mkw 0x05c0200014ead7e0 0xf02e010000a756bf 0x000800000fffffff 0xe0004000007fffff

def z1063 : W := mkw 0x0440200014e24620 0x5022010000a71231 0x000000000de64e77 0xe0000000006f3273

def z1064 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1ec7fe000ffe0002 0xc0f63ff0007ff000

def z1065 : W := mkw 0x0400200004c00000 0x0020010000260000 0x1fe7fe000ffe0003 0xe0ff3ff0007ff000

def z1066 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xecd7fffff0000000 0x1f66bfffff800000

def z1067 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0xbfe7ff99f0000000 0x1dff3ffccf800000

def z1068 : W := mkw 0x10400208b0224620 0x5082001045811231 0xaaa10619f1464e76 0xbd550830cf8a3273

def z1069 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80fb9fc1f 0xef0ff80fc07dcfe0

def z1070 : W := mkw 0x4e8721501ffd7a8b 0x6274390a80ffebd4 0xe1ff01f80fffff9f 0xef0ff80fc07ffffc

def z1071 : W := mkw 0xf117dfffe000815c 0x8788beffff00040a 0xfff7fffff00003e0 0x1fffbfffff80001f

def z1072 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xfff7fe780ffe7c1f 0xefffbff3c07ff3e0

def z1073 : W := mkw 0x10400208b0224620 0x5082001045811231 0x9a810619f1664e77 0xb4d40830cf8b3273

def z1074 : W := mkw 0xf217dfffe014001d 0x0790beffff00a000 0xfff7fffff03e0000 0x1fffbfffff81f000

def z1075 : W := mkw 0x00c00822502a56a0 0x70060041128152b5 0x7ff31e6673fe7fff 0xfbff98f3339ff3ff

def z1076 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1ff7fe600ffe7003 0xe8ffbff3007ff380

def z1077 : W := mkw 0xc80795500b01281a 0x06403caa80580940 0xe5fff9f80f01fc1d 0xef2fffcfc0780fe0

def z1078 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1ff7fe7ff0000000 0x18ffbff3ff800000

def z1079 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fa5fe000dfe0003 0xa0fd2ff0006ff000

def z1080 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xf997fffff0000000 0x1fccbfffff800000

def z1081 : W := mkw 0x200048a740000004 0x010002453a000000 0xeef4e1e7f0000000 0x1f77a70f3f800000

def z1082 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80f67fc1f 0xef0ff80fc07b3fe0

def z1083 : W := mkw 0x90079608a0000010 0x04803cb045000000 0xbba5e619f0000000 0x1ddd2f30cf800000

def z1084 : W := mkw 0x2500608504c08144 0x812803042826040a 0xefede1878dc183ff 0xf77f6f0c3c6e0c1f

def z1085 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0xe1ff19f80f19fc1d 0xef0ff8cfc078cfe0

def z1086 : W := mkw 0x8e07b4000fd52813 0x04703da0007ea940 0xbfeffe180ffffc1f 0xedff7ff0c07fffe0

def z1087 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0xfff7fff8033e7c01 0x0fffbfffc019f3e0

def z1088 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbbad0799fd67ce77 0xbddd683ccfeb3e73

def z1089 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878cc183ea 0x5777670c3c660c1f

def z1090 : W := mkw 0x0080082250285280 0x6004004112814294 0x4452186672983388 0x522290c33394c19c

def z1091 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x7fe7fe060ffe0003 0xf3ff3ff0307ff000

def z1092 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e84fe000cfe0002 0x80f427f00067f000

def z1093 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0x555ffffe7f01fc09 0x4aaafffff3f80fe0

def z1094 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1987fe00033e0001 0x00cc3ff00019f000

def z1095 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xfff5e7fff0000000 0x1fffaf3fff800000

def z1096 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfff7ffffff007c01 0xffffbffffff803e0

def z1097 : W := mkw 0x4a0701500b15280b 0x0250380a8058a940 0xe1ff01f80f3ffc1d 0xef0ff80fc079ffe0

def z1098 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0xff72fffff0000000 0x1ffb97ffff800000

def z1099 : W := mkw 0xe817ddf74b01281e 0x0740beefba580940 0xf7fff9fe7f01fc1d 0xffbfffcff3f80fe0

def z1100 : W := mkw 0xf017dfffe001281c 0x0780beffff000940 0xfffffffff001b008 0x1fffffffff800d80

def z1101 : W := mkw 0x10400208b0224620 0x5082001045811231 0x9b810619f1664e73 0x9cdc0830cf8b3273

def z1102 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffffc81839e 0xffffffffffe40c1c

def z1103 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xbfa1fe1ff1004c15 0xbdfd0ff0ff880260

def z1104 : W := mkw 0x90109e2ae0000010 0x048084f157000000 0x1e00fe0070000000 0x00f007f003800000

def z1105 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000f7e0001 0x80ff3ff0007bf000

def z1106 : W := mkw 0xf097dfffe008109c 0x2784beffff004084 0xfff7fffff2183000 0x1fffbfffff90c180

def z1107 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe44ce1878cc183fe 0xf722670c3c660c1f

def z1108 : W := mkw 0x8f07b4000fd48153 0x84783da0007ea40a 0x1fe7fe000ffe03e3 0xe0ff3ff0007ff01f

def z1109 : W := mkw 0x10400208b0224620 0x5082001045811231 0xb1010619f1664e77 0xbd880830cf8b3273

def z1110 : W := mkw 0x0080082250285280 0x6004004112814294 0x7552186672b8738d 0x5baa90c33395c39c

def z1111 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xe45ef9fffe01fc1c 0x5f22f7cffff00fe0

def z1112 : W := mkw 0xb017deafe0000014 0x0580bef57f000000 0x7ff7fe67f0000000 0x1bffbff33f800000

def z1113 : W := mkw 0x3000428da0000004 0x018002146d000000 0xeee4e19ff0000000 0x1f77270cff800000

def z1114 : W := mkw 0xf917dfffeb01a95e 0x87c8beffff580d4a 0xffffffffff01fffd 0xfffffffffff80fff

def z1115 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x3fe7fe000ffe0207 0xf1ff3ff0007ff010

def z1116 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0c003fe 0xffffbfffff86001f

def z1117 : W := mkw 0x0540200014e2c760 0xd02a010000a7163b 0x000800000cc1cffe 0xe000400000660e7f

def z1118 : W := mkw 0x0080082250285280 0x6004004112814294 0x777218667298738c 0x5bbb90c33394c39c

def z1119 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1400fe0000be0000 0x00a007f00005f000

def z1120 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7ffffff660003 0xffffbffffffb3000

def z1121 : W := mkw 0x2040408510224624 0x5102020428811231 0xeee4e18781664e77 0xb777270c3c0b3273

def z1122 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x5ff7fe600ffe300b 0xe2ffbff3007ff180

def z1123 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0x7ff7fe7e70000000 0x1bffbff3f3800000

def z1124 : W := mkw 0x8e00b4000fd40013 0x047005a0007ea000 0x1e00fe0003fe0003 0x00f007f0001ff000

def z1125 : W := mkw 0x0080082250285280 0x6004004112814294 0x77f618667eb8738f 0xfbbfb0c333f5c39c

def z1126 : W := mkw 0x0640200014f64621 0x5032010000a7b231 0x0000000001fe4e77 0xa0000000000ff273

def z1127 : W := mkw 0xba17deafeb140017 0x05d0bef57f58a000 0x1f03fe07f33e0001 0x10f81ff03f99f000

def z1128 : W := mkw 0x10c00208b02a56a0 0x70860010458152b5 0xbba10619f1fe4ff7 0xbddd0830cf8ff27f

def z1129 : W := mkw 0x8e07b4000fd52813 0x04703da0007ea940 0x1feffe000fff8c13 0xe0ff7ff0007ffc60

def z1130 : W := mkw 0x0580200014e8d3c0 0xe02c010000a7469e 0x000800000cc1f3fe 0xe000400000660f9f

def z1131 : W := mkw 0x480001500b01280a 0x0240000a80580940 0xe1b901f80f01fc1d 0xef0dc80fc0780fe0

def z1132 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x999ffff80f7ffc11 0x8cccffffc07bffe0

def z1133 : W := mkw 0x8607b40004d40011 0x04303da00026a000 0x1fe7fe0002fe0003 0x60ff3ff00017f000

def z1134 : W := mkw 0x0080082250285280 0x6004004112814294 0xfff21867f2b8738f 0x7fff90c33f95c39c

def z1135 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff01b009 0xfffffffffff80d80

def z1136 : W := mkw 0x0080082250285280 0x6004004112814294 0xf77a19e672b9f39f 0x7fbbd0cf3395cf9c

def z1137 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1460000 0x9fffbfffff8a3000

def z1138 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0x1e10fe7ff0000000 0x18f087f3ff800000

def z1139 : W := mkw 0x0500200014e0c340 0xc028010000a7061a 0x000800000ce1c3ff 0xe000400000670e1f

def z1140 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878c8183fc 0x5777670c3c640c1f

def z1141 : W := mkw 0x10000208a0000000 0x0080001045000000 0xbfe5e619f0000000 0x1dff2f30cf800000

def z1142 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1f62fe07f0000000 0x10fb17f03f800000

def z1143 : W := mkw 0x0080082250285280 0x6004004112814294 0xf7ff19fe7fb9ff9f 0xffbff8cff3fdcffc

def z1144 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1660277 0xbfffbfffff8b3013

def z1145 : W := mkw 0x0ec020001ffe56a3 0x7076010000fff2b5 0x000000000ffe7fff 0xe0000000007ff3ff

def z1146 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1f02fe0002fe0003 0x00f817f00017f000

def z1147 : W := mkw 0x0080082250285280 0x6004004112814294 0x7773187e73b87f8f 0x7bbb98c3f39dc3fc

def z1148 : W := mkw 0x4007015000012808 0x0200380a80000940 0xe1ff01f80c01fc1c 0xef0ff80fc0600fe0

def z1149 : W := mkw 0x35c06aaff4ead7e4 0xf1ae03557fa756bf 0x1e00fe07f0fe03e2 0x10f007f03f87f01f

def z1150 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x5fefff800fff800b 0xe2ff7ffc007ffc00

def z1151 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeefee1e78ec1b3fe 0xf777f70f3c760d9f

def z1152 : W := mkw 0x3000428da0000004 0x018002146d000000 0xfee4e787f0000000 0x17f7273c3f800000

def z1153 : W := mkw 0x2500608504c08144 0x812803042826040a 0xcccce1878cc183fe 0xe666670c3c660c1f

def z1154 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe09d01f80f01fc1d 0xef04e80fc0780fe0

def z1155 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x1fe7fe180ffe0c03 0xe0ff3ff0c07ff060

def z1156 : W := mkw 0xb010d68da0000014 0x058086b46d000000 0xbba1e619f0000000 0x1ddd0f30cf800000

def z1157 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1e01fe0001fe0002 0x00f00ff0000ff000

def z1158 : W := mkw 0x0640200014f64621 0x5032010000a7b231 0x0000000000fe0262 0x000000000007f013

def z1159 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x9ffffff80ffffc13 0xecffffffc07fffe0

def z1160 : W := mkw 0x0080082250285280 0x6004004112814294 0xfff31e67f3fe73ff 0xffff98f33f9ff39f

def z1161 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfff31e79f3fe7e7f 0xffff98f3cf9ff3f3

def z1162 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe09c01f80c01fc1c 0x8f04e00fc0600fe0

def z1163 : W := mkw 0x4e4721501ff76e2b 0x5272390a80ffbb71 0xe1ff01f80ffffe7f 0xef0ff80fc07ffff3

def z1164 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0004005 0x3fffbfffff800200

def z1165 : W := mkw 0x10400208b0224620 0x5082001045811231 0xffe31e1ff3fe4fff 0xffff18f0ff9ff27f

def z1166 : W := mkw 0xf017dfffe001281c 0x0780beffff000940 0xfff7fffff0007c00 0x1fffbfffff8003e0

def z1167 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1b010619f1664e77 0xb8d80830cf8b3273

def z1168 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba31e19f37e4e77 0xbddd18f0cf9bf273

def z1169 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x5ff7fffe70000000 0x0affbffff3800000

def z1170 : W := mkw 0x8607b40004d40011 0x04303da00026a000 0x1f03fe0000fe0002 0x00f81ff00007f000

def z1171 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe7ff01fe0f01fc1d 0xff3ff80ff0780fe0

def z1172 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffffb9fc1f 0xfffffffffffdcfe0

def z1173 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1004c01 0x1fffbfffff880260

def z1174 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x7e10fe67f0000000 0x1bf087f33f800000

def z1175 : W := mkw 0x0080082250285280 0x6004004112814294 0x77f3186673b8738f 0xfbbf98c3339dc39c

def z1176 : W := mkw 0x70104bffe001280c 0x0380825fff000940 0xeefce1fffc01fc1c 0xff77e70fffe00fe0

def z1177 : W := mkw 0xb010d68da0000014 0x058086b46d000000 0x1a00e601f0000000 0x10d007300f800000

def z1178 : W := mkw 0x10400208a0020420 0x1082001045001021 0xbba10619f1660c73 0xbddd0830cf8b3063

def z1179 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e44fe000cfe0002 0x40f227f00067f000

def z1180 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0x999ffff9ff01fc11 0x8cccffffcff80fe0

def z1181 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xbbb7fff9f0000000 0x1dddbfffcf800000

def z1182 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e00fe0600fe0382 0x10f007f03007f01c

def z1183 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfbe50799f1664e77 0xbfdf283ccf8b3273

def z1184 : W := mkw 0xf097dfffe008109c 0x2784beffff004084 0xfff7fffff2b8318b 0x7fffbfffff95c18c

def z1185 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x4456f9fe70000000 0x0a22b7cff3800000

def z1186 : W := mkw 0xf117dfffe001a95c 0x8788beffff000d4a 0xfffffffff001fffc 0x1fffffffff800fff

def z1187 : W := mkw 0x8f07b4000fd48153 0x84783da0007ea40a 0x1feffe000fff818b 0xe0ff7ff0007ffc0c

def z1188 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x7f73fe7ff0000000 0x1bfb9ff3ff800000

def z1189 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeeef9878ed983fe 0xf77777cc3c76cc1f

def z1190 : W := mkw 0xf817d7ddab01281e 0x07c0bebeed580940 0xbbade799fd01cc15 0xbddd6f3ccfe80e60

def z1191 : W := mkw 0xf857dfffeb032c3e 0x17c2beffff581961 0xffffffffff47fc7d 0xfffffffffffa3fe3

def z1192 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878dc1cfff 0xf777670c3c6e0e7f

def z1193 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0660002 0x1fffbfffff833000

def z1194 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xfffffff98ffffe7f 0xffffffffcc7ffff3

def z1195 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80e01fc1c 0x4f0ff80fc0700fe0

def z1196 : W := mkw 0x3000428da0000004 0x018002146d000000 0xbfa1e61ff0000000 0x1dfd0f30ff800000

def z1197 : W := mkw 0x2500608504c08144 0x812803042826040a 0x6e6ce1878cc183ee 0x7373670c3c660c1f

def z1198 : W := mkw 0x1e002208afd40003 0x00f00110457ea000 0xbba10619fffe0003 0xfddd0830cffff000

def z1199 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffc018000 0x1fffffffffe00c00

def z1200 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xe9ffe7ffff01fc1d 0xff4fff3ffff80fe0

def z1201 : W := mkw 0x10400208a0020420 0x1082001045001021 0xbba10619f1460e76 0xbddd0830cf8a3073

def z1202 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffede7878cc183fe 0xf7ff6f3c3c660c1f

def z1203 : W := mkw 0x10400208b0224620 0x5082001045811231 0x3b210619f1664e67 0x39d90830cf8b3273

def z1204 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1885fe000d7e0000 0x80c42ff0006bf000

def z1205 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1446fe000ebe0000 0x40a237f00075f000

def z1206 : W := mkw 0xa007dca740000014 0x05003ee53a000000 0xfff7ffe7f0000000 0x1fffbfff3f800000

def z1207 : W := mkw 0x0080082250285280 0x6004004112814294 0x657218667298738d 0x7b2b90c33394c39c

def z1208 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfff3067ff3e67fff 0xffff9833ff9f33ff

def z1209 : W := mkw 0xfa17dfffeb14001f 0x07d0beffff58a000 0xfff7fffff1060000 0x1fffbfffff883000

def z1210 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xf5f7fffe70000000 0x0fafbffff3800000

def z1211 : W := mkw 0x2500608504c08144 0x812803042826040a 0xee4ce1878cc183fe 0x5772670c3c660c1f

def z1212 : W := mkw 0x0480200014e85280 0x6024010000a74294 0x000000000ef8738f 0xe00000000077c39c

def z1213 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2007001 0x1fffbfffff900380

def z1214 : W := mkw 0x0080082250285280 0x6004004112814294 0x7ff31e6672b8738f 0x7bff98f33395c39c

def z1215 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfff7fffff1000c00 0x1fffbfffff880060

def z1216 : W := mkw 0x0080082250285280 0x6004004112814294 0xfffe19e7fef9f3ff 0xfffff0cf3ff7cf9f

def z1217 : W := mkw 0x10400208b0224620 0x5082001045811231 0xffe1061ff1664e77 0xbfff0830ff8b3273

def z1218 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbbb30679f3667e77 0xbddd9833cf9b33f3

def z1219 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0x9e8dff9ffd018c10 0x94f46ffcffe80c60

def z1220 : W := mkw 0xce07b5500fd4001b 0x06703daa807ea000 0x9fe7ff980ffe0003 0xe4ff3ffcc07ff000

def z1221 : W := mkw 0x0080082250285280 0x6004004112814294 0x7f721867f2f873ef 0x7bfb90c33f97c39f

def z1222 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe11b01f80f01fc1d 0xef08d80fc0780fe0

def z1223 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1fe6fe000efe0003 0xe0ff37f00077f000

def z1224 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xffffffe00fffb01f 0xe7ffffff007ffd80

def z1225 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1fe3fe0003fe0003 0xe0ff1ff0001ff000

def z1226 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f3667e7f 0xfddd0830cf9b33f3

def z1227 : W := mkw 0x8607b40004d40011 0x04303da00026a000 0x1e46fe0000fe0002 0x00f237f00007f000

def z1228 : W := mkw 0x258068a754e8d3c4 0xe12c03453aa7469e 0x999ef9e1fe79f071 0x8cccf7cf0ff3cf83

def z1229 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe1fe01f80e01fc1d 0xef0ff00fc0700fe0

def z1230 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2380001 0x1fffbfffff91c000

def z1231 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xbfb3fe7ff0000000 0x1dfd9ff3ff800000

def z1232 : W := mkw 0x8700b40004d48151 0x843805a00026a40a 0x1e00fe0000fe03e2 0x00f007f00007f01f

def z1233 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1fe7fe0003be0003 0x60ff3ff0001df000

def z1234 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfe95fffff0000000 0x1ff4afffff800000

def z1235 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1ee5fe000dfe0002 0xe0f72ff0006ff000

def z1236 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f98f01fe7d 0xff0ff80fcc780ff3

def z1237 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0x9a85e799f0000000 0x14d42f3ccf800000

def z1238 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xf9f7fff9f0000000 0x0fcfbfffcf800000

def z1239 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2003008 0x5fffbfffff900180

def z1240 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0x9985e799f0000000 0x0ccc2f3ccf800000

def z1241 : W := mkw 0x8007940000000010 0x04003ca000000000 0x3fe7fe0070000000 0x19ff3ff003800000

def z1242 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x7777fffe70000000 0x1bbbbffff3800000

def z1243 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1a010619f1660e62 0x10d00830cf8b3073

def z1244 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff2000001 0x7fffbfffff900000

def z1245 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1e85fe000ffe0003 0xe0f42ff0007ff000

def z1246 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x1f13fe7803fe7c03 0x08f89ff3c01ff3e0

def z1247 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x5456ffe670000000 0x02a2b7ff33800000

def z1248 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x9e84ff87f0000000 0x14f427fc3f800000

def z1249 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1f62fe0000fe0002 0x00fb17f00007f000

def z1250 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0xfbff1ff80f7ffc1f 0xefdff8ffc07bffe0

def z1251 : W := mkw 0x8e07b4000fd52813 0x04703da0007ea940 0x1feffe000fffb00b 0xe0ff7ff0007ffd80

def z1252 : W := mkw 0xb210deafe0140015 0x059086f57f00a000 0x1e00fe07f03e0000 0x10f007f03f81f000

def z1253 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x7ff7fe660ffe738f 0xfbffbff3307ff39c

def z1254 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x3fe7fe007ffe0003 0xf9ff3ff003fff000

def z1255 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfff7fffff2003000 0x1fffbfffff900180

def z1256 : W := mkw 0x8607b40004d40011 0x04303da00026a000 0x1fe7fe000cfe0002 0xe0ff3ff00067f000

def z1257 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x9fe7ff9ff0000000 0x14ff3ffcff800000

def z1258 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xf1ff19f80f39fc1d 0xef8ff8cfc079cfe0

def z1259 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1903fe00037e0001 0x00c81ff0001bf000

def z1260 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1e12fe67f0000000 0x10f097f33f800000

def z1261 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xfff6f9fff0000000 0x1fffb7cfff800000

def z1262 : W := mkw 0x4000015000012808 0x0200000a80000940 0xe1fd01f80d01fc1d 0xef0fe80fc0680fe0

def z1263 : W := mkw 0x8e00b4000fd40013 0x047005a0007ea000 0x1fa1fe000ffe0003 0xe0fd0ff0007ff000

def z1264 : W := mkw 0x10400208b0224620 0x5082001045811231 0x9ba10619f1660e73 0xb4dd0830cf8b3073

def z1265 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeccce1878cc183fc 0xd766670c3c660c1f

def z1266 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1e04fe000cfe0002 0x00f027f00067f000

def z1267 : W := mkw 0x200048a740000004 0x010002453a000000 0x1e00f807f0000000 0x10f007c03f800000

def z1268 : W := mkw 0x3000428da0000004 0x018002146d000000 0xffede79ffd01cc1d 0xffff6f3cffe80e60

def z1269 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff000700c 0x1fffbfffff800380

def z1270 : W := mkw 0x8e07b4000fd52813 0x04703da0007ea940 0x1fe7fe000ffe7c03 0xe0ff3ff0007ff3e0

def z1271 : W := mkw 0xf010dfffe001281c 0x078086ffff000940 0xfe18fffff001fc1c 0x1ff0c7ffff800fe0

def z1272 : W := mkw 0x2500608504c08144 0x812803042826040a 0x8eece1878cc183f2 0xf477670c3c660c1f

def z1273 : W := mkw 0xc80795500b01281a 0x06403caa80580940 0xe9ffe7f80f01fc1d 0xef4fff3fc0780fe0

def z1274 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xf5fffff80fbffc1d 0xefafffffc07dffe0

def z1275 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xebff01f98f01fc1d 0xff5ff80fcc780fe0

def z1276 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xbfe7fe180ffe0003 0xedff3ff0c07ff000

def z1277 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe3ff01f80f01fe1f 0xff1ff80fc0780ff0

def z1278 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe7ff01f80f81fc1f 0xef3ff80fc07c0fe0

def z1279 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1107fe000f3e0001 0x00883ff00079f000

def z1280 : W := mkw 0x2500608504c08144 0x812803042826040a 0xfeecf9878cf983fe 0xf7f767cc3c67cc1f

def z1281 : W := mkw 0xe817ddf74b01281e 0x0740beefba580940 0x777ef9e67e01f00d 0x7bbbf7cf33f00f80

def z1282 : W := mkw 0x8e87bc225ffc5293 0x64743de112ffe294 0x6895e6667d46738c 0x9b44af3333ea339c

def z1283 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xffe5ff9ff0000000 0x1fff2ffcff800000

def z1284 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878cc183f2 0x9777670c3c660c1f

def z1285 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffffc018008 0x5fffffffffe00c00

def z1286 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0x1557fe7870000000 0x08aabff3c3800000

def z1287 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff000000c 0x7fffbfffff800000

def z1288 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xefff01ff8fc1ffff 0xff7ff80ffc7e0fff

def z1289 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01f80f81ff9f 0xef0ff80fc07c0ffc

def z1290 : W := mkw 0x600749f74000000c 0x03003a4fba000000 0xfff7f9fff0000000 0x1fffbfcfff800000

def z1291 : W := mkw 0xf057dfffe002043c 0x1782beffff001021 0xfff7fffff1460e76 0xbfffbfffff8a3073

def z1292 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xe89de7fffd01fc1c 0x9f44ef3fffe80fe0

def z1293 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1ff01fe0f01ff9d 0xff0ff80ff0780ffc

def z1294 : W := mkw 0xb017deafe0000014 0x0580bef57f000000 0xffe7ff87f0000000 0x17ff3ffc3f800000

def z1295 : W := mkw 0x0000082240000000 0x0000004112000000 0x7ff6f86670000000 0x1bffb7c333800000

def z1296 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7ffffff00700d 0xffffbffffff80380

def z1297 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fa3fe0003fe0003 0xa0fd1ff0001ff000

def z1298 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe5ff01fe0f81fd9d 0xef2ff80ff07c0fec

def z1299 : W := mkw 0xf097dfffe008109c 0x2784beffff004084 0xfff7fffff0980180 0x1fffbfffff84c00c

def z1300 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x9fefff800fff8013 0xe4ff7ffc007ffc00

def z1301 : W := mkw 0x70104bffe000000c 0x0380825fff000000 0xee10e1fff0000000 0x1f70870fff800000

def z1302 : W := mkw 0x2500608504c08144 0x812803042826040a 0x8e8ce1878cc183fe 0xf474670c3c660c1f

def z1303 : W := mkw 0x90079608a0000010 0x04803cb045000000 0x1fe7fe1870000000 0x08ff3ff0c3800000

def z1304 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbaa10619f1660e76 0xb5d50830cf8b3073

def z1305 : W := mkw 0x200048a740000004 0x010002453a000000 0x7776f9e670000000 0x1bbbb7cf33800000

def z1306 : W := mkw 0x0e4720001ff64623 0x5072390000ffb231 0xa1e700180ffe4e77 0xed0f3800c07ff273

def z1307 : W := mkw 0x8e00b4000fd40013 0x047005a0007ea000 0x1ee4fe000ffe0003 0xe0f727f0007ff000

def z1308 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbfe5e619f1664e77 0xbdff2f30cf8b3273

def z1309 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1dc7fe000ffe0001 0xc0ee3ff0007ff000

def z1310 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0xfeecff800cff801e 0xe7f767fc0067fc00

def z1311 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x3fe7fe000ffe4007 0xe9ff3ff0007ff200

def z1312 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xdffffff80fffbc1b 0xe6ffffffc07ffde0

def z1313 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xf776f9fff0000000 0x1fbbb7cfff800000

def z1314 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbfa11e19f1fe4e77 0xbdfd08f0cf8ff273

def z1315 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x5e44ff87f0000000 0x12f227fc3f800000

def z1316 : W := mkw 0x0080082250285280 0x6004004112814294 0x5452186672b83188 0x42a290c33395c18c

def z1317 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x5fe7fe060ffe018b 0xe2ff3ff0307ff00c

def z1318 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0x9e00ff9ff0000000 0x14f007fcff800000

def z1319 : W := mkw 0x2500608504c08144 0x812803042826040a 0xee8ce1878cc183fe 0x9774670c3c660c1f

def z1320 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffffc018010 0x9fffffffffe00c00

def z1321 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x7ff7fe780ffe7c0f 0xebffbff3c07ff3e0

def z1322 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x5e5effe00effb00a 0x42f2f7ff0077fd80

def z1323 : W := mkw 0x8207940000140011 0x04103ca00000a000 0x1fe7fe00003e0000 0x00ff3ff00001f000

def z1324 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0000014 0xbfffbfffff800000

def z1325 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xbea0fe07f0400276 0xb5f507f03f820013

def z1326 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x19e7fe000f7e0001 0xe0cf3ff0007bf000

def z1327 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe9ff07f80f47fc1d 0xef4ff83fc07a3fe0

def z1328 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbba10619f1660e72 0x9ddd0830cf8b3073

def z1329 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe1bd01f80d01fc1d 0xaf0de80fc0680fe0

def z1330 : W := mkw 0x0080082250285280 0x6004004112814294 0x7712186672b8738f 0x1bb890c33395c39c

def z1331 : W := mkw 0xc80795500b01281a 0x06403caa80580940 0xfffffff80f67fc1f 0xefffffffc07b3fe0

def z1332 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0400070 0x9fffbfffff820003

def z1333 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1000c10 0x9fffbfffff880060

def z1334 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000ffe038f 0xe0ff3ff0007ff01c

def z1335 : W := mkw 0xf017dfffe001281c 0x0780beffff000940 0xfffffffff101fc1d 0xbfffffffff880fe0

def z1336 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x9fe7fe018ffe0073 0xe4ff3ff00c7ff003

def z1337 : W := mkw 0xc80795500b01281a 0x06403caa80580940 0xf1ff1ff80f01fc1d 0xef8ff8ffc0780fe0

def z1338 : W := mkw 0x0540200014e2c760 0xd02a010000a7163b 0xe1ed01980de7cfff 0xef0f680cc06f3e7f

def z1339 : W := mkw 0xd8179f7aeb01281a 0x06c0bcfbd7580940 0xfffffff87f01fc1d 0xefffffffc3f80fe0

def z1340 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x617f01f80f01fc0d 0x6b0bf80fc0780fe0

def z1341 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xffefff818fff827f 0xf7ff7ffc0c7ffc13

def z1342 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x5fffffe00ffffc1f 0xe2ffffff007fffe0

def z1343 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x8895e7f9f0000000 0x0c44af3fcf800000

def z1344 : W := mkw 0x8e00b4000fd40013 0x047005a0007ea000 0x1e00fe000dfe0002 0x80f007f0006ff000

def z1345 : W := mkw 0xa010dca740000014 0x050086e53a000000 0x7772f86670000000 0x1bbb97c333800000

def z1346 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0000274 0x1fffbfffff800013

def z1347 : W := mkw 0x8700b40004d48151 0x843805a00026a40a 0x1e08fe000cff83fe 0xe0f047f00067fc1f

def z1348 : W := mkw 0xce07b5500fd4001b 0x06703daa807ea000 0xfffffff80fff801f 0xefffffffc07ffc00

def z1349 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0x1f13fe7ff3007c01 0x18f89ff3ff9803e0

def z1350 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x7fe7fe000ffe000f 0xe3ff3ff0007ff000

def z1351 : W := mkw 0x0e8020001ffc5283 0x6074010000ffe294 0x000000000ffe0383 0xe0000000007ff01c

def z1352 : W := mkw 0x0080082250285280 0x6004004112814294 0x5552186672b8738f 0x6aaa90c33395c39c

def z1353 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xfe00ff87f0000000 0x17f007fc3f800000

def z1354 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbfa1061ff1e64ff7 0xbdfd0830ff8f327f

def z1355 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1e00fe07f0660002 0x10f007f03f833000

def z1356 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7fffff3000001 0x1fffbfffff980000

def z1357 : W := mkw 0x80009c2240000010 0x040004e112000000 0x1e00fe0670000000 0x10f007f033800000

def z1358 : W := mkw 0xcf07b5500fd5a95b 0x86783daa807ead4a 0xfffffff80fffffff 0xefffffffc07fffff

def z1359 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xe5fff9ffff01fc1d 0xff2fffcffff80fe0

def z1360 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1400fe0670000000 0x00a007f033800000

def z1361 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186673fe738f 0xfbbb90c3339ff39c

def z1362 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e00fe0001fe0003 0xa0f007f0000ff000

def z1363 : W := mkw 0x2500608504c08144 0x812803042826040a 0xe88ce1878cc183fe 0xf744670c3c660c1f

def z1364 : W := mkw 0xce07b5500fd4001b 0x06703daa807ea000 0xfff7fff80ffe4c17 0xefffbfffc07ff260

def z1365 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1f66fe000efe0003 0x60fb37f00077f000

def z1366 : W := mkw 0x3000428da0000004 0x018002146d000000 0xbba5e799f0000000 0x1ddd2f3ccf800000

def z1367 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1f63fe0003fe0003 0x60fb1ff0001ff000

def z1368 : W := mkw 0x80079c2240000010 0x04003ce112000000 0x7776f86670000000 0x1bbbb7c333800000

def z1369 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xa1bf01f80f01fc15 0xad0df80fc0780fe0

def z1370 : W := mkw 0x8f07b4000fd48153 0x84783da0007ea40a 0x1feffe000fff8073 0xe0ff7ff0007ffc03

def z1371 : W := mkw 0x8f07b4000fd48153 0x84783da0007ea40a 0xbfeffe018fff83ff 0xf5ff7ff00c7ffc1f

def z1372 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfba90799f167ce7f 0xbfdd483ccf8b3e73

def z1373 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe15f01f80f01fc1d 0x4f0af80fc0780fe0

def z1374 : W := mkw 0xca0795500b15281b 0x06503caa8058a940 0xe1ff07f80f07fc1d 0xef0ff83fc0783fe0

def z1375 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0xf7f7f9fe70000000 0x1fbfbfcff3800000

def z1376 : W := mkw 0x0080082240081080 0x2004004112004084 0x7772186672b8318b 0x7bbb90c33395c18c

def z1377 : W := mkw 0x00c00822502a56a0 0x70060041128152b5 0x7772186673be7f8f 0x7bbb90c3339df3fc

def z1378 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbbe50619fd664e77 0xfddf2830cfeb3273

def z1379 : W := mkw 0x2500608504c08144 0x812803042826040a 0xffeef9878cc183fe 0xf7ff77cc3c660c1f

def z1380 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe180ffe4c03 0xe8ff3ff0c07ff260

def z1381 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e42fe0002fe0002 0x40f217f00017f000

def z1382 : W := mkw 0x8e07b4000fd52813 0x04703da0007ea940 0x7ffffe600ffffc1f 0xebfffff3007fffe0

def z1383 : W := mkw 0xd8079758ab01281a 0x06c03cbac5580940 0xfffffff9ff01fc1d 0xffffffffcff80fe0

def z1384 : W := mkw 0xd0179f7ae0000018 0x0680bcfbd7000000 0x1f13fe7870000000 0x08f89ff3c3800000

def z1385 : W := mkw 0x0500282244c08140 0x802801411226040a 0x777a18667cc183fe 0xfbbbd0c333e60c1f

def z1386 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1f03fe000ffe0003 0xe0f81ff0007ff000

def z1387 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x1e01fe1ff0000000 0x10f00ff0ff800000

def z1388 : W := mkw 0x0080082250285280 0x6004004112814294 0x1612186672b83382 0x10b090c33395c19c

def z1389 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1767fe000fbe0003 0x60bb3ff0007df000

def z1390 : W := mkw 0x8a0794000b140013 0x04503ca00058a000 0x1fe7fe00037e0003 0xa0ff3ff0001bf000

def z1391 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1f20fe0000fe0003 0x20f907f00007f000

def z1392 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186672b87383 0x1bbb90c33395c39c

def z1393 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0400002 0xbfffbfffff820000

def z1394 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfe56fffff0000000 0x1ff2b7ffff800000

def z1395 : W := mkw 0x30004aafe0000004 0x018002557f000000 0xfff7fffff0000000 0x1fffbfffff800000

def z1396 : W := mkw 0x0540200014e2c760 0xd02a010000a7163b 0x000800000ce783fe 0xe000400000673c1f

def z1397 : W := mkw 0x80079c2240000010 0x04003ce112000000 0x1ff7fe6070000000 0x08ffbff303800000

def z1398 : W := mkw 0x0080082250285280 0x6004004112814294 0x7672186672b8338e 0x73b390c33395c19c

def z1399 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0x5656f9e670000000 0x12b2b7cf33800000

def z1400 : W := mkw 0x88079c224b000012 0x04403ce112580000 0x7ff7fe667f00700d 0xfbffbff333f80380

def z1401 : W := mkw 0x10c00208b02a56a0 0x70860010458152b5 0xbfe31e19f3fe7fff 0xfdff18f0cf9ff3ff

def z1402 : W := mkw 0x90079e2ae0000010 0x04803cf157000000 0xfff7fe7ff0000000 0x1fffbff3ff800000

def z1403 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeede19f8dc18ffe 0xf7776f0cfc6e0c7f

def z1404 : W := mkw 0x0080082250285280 0x6004004112814294 0x5772186672b8338b 0x72bb90c33395c19c

def z1405 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0000206 0x3fffbfffff800010

def z1406 : W := mkw 0x0080082250285280 0x6004004112814294 0x7572186672b8718d 0x6bab90c33395c38c

def z1407 : W := mkw 0xe017ddf74000001c 0x0700beefba000000 0x5556f9e670000000 0x0aaab7cf33800000

def z1408 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe0fe01f80e01fc1c 0xef07f00fc0700fe0

def z1409 : W := mkw 0x480001500b01280a 0x0240000a80580940 0xe0fc01f80f01fc1d 0xef07e00fc0780fe0

def z1410 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffd01cc15 0xbfffffffffe80e60

def z1411 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffe01f00d 0x7ffffffffff00f80

def z1412 : W := mkw 0x680749f74b01280e 0x03403a4fba580940 0xfffff9ffff01fc1d 0xffffffcffff80fe0

def z1413 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7fffffe000000 0x5fffbffffff00000

def z1414 : W := mkw 0x480001500b01280a 0x0240000a80580940 0xe01801f80d01fc1c 0x8f00c00fc0680fe0

def z1415 : W := mkw 0xf117dfffe000815c 0x8788beffff00040a 0xfffffffff04183fe 0xbfffffffff820c1f

def z1416 : W := mkw 0xb017deafe0000014 0x0580bef57f000000 0x1e85fe07f0000000 0x10f42ff03f800000

def z1417 : W := mkw 0x8e00b4000fd40013 0x047005a0007ea000 0x1e00fe000efe0002 0x40f007f00077f000

def z1418 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0400262 0x1fffbfffff820013

def z1419 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff1260001 0x1fffbfffff893000

def z1420 : W := mkw 0x0080082250285280 0x6004004112814294 0x5652186672b8738f 0x72b290c33395c39c

def z1421 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x9885ff99f0000000 0x04c42ffccf800000

def z1422 : W := mkw 0x0080082250285280 0x6004004112814294 0xf7f2186672b8739f 0xffbf90c33395c39c

def z1423 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff01fc09 0x5ffffffffff80fe0

def z1424 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfff7fffff3007c0d 0x7fffbfffff9803e0

def z1425 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1e46fe000ffe0003 0xe0f237f0007ff000

def z1426 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffffe01f01d 0xfffffffffff00f80

def z1427 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe0fd01f80d01fc1c 0xef07e80fc0680fe0

def z1428 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x555ffff80fbffc09 0x4aaaffffc07dffe0

def z1429 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xf7ff19f80f01fc1d 0xefbff8cfc0780fe0

def z1430 : W := mkw 0x0e4020001ff64623 0x5072010000ffb231 0x000000000d664e77 0xa0000000006b3273

def z1431 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x405e01f80e01fc08 0x4a02f00fc0700fe0

def z1432 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xffffffe00ffff01f 0xefffffff007fff80

def z1433 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff000038c 0x1fffbfffff80001c

def z1434 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xffefff860fff839f 0xf7ff7ffc307ffc1c

def z1435 : W := mkw 0x8e00b4000fd40013 0x047005a0007ea000 0x1f62fe000ffe0003 0xe0fb17f0007ff000

def z1436 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffd01fc1c 0x9fffffffffe80fe0

def z1437 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878ef983ff 0xf777670c3c77cc1f

def z1438 : W := mkw 0x8600b40004d40011 0x043005a00026a000 0x1e00fe0002fe0003 0x60f007f00017f000

def z1439 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xbff7fe780ffe7c17 0xedffbff3c07ff3e0

def z1440 : W := mkw 0xfa17dfffeb15281f 0x07d0beffff58a940 0xffffffffff3ffc1d 0xfffffffffff9ffe0

def z1441 : W := mkw 0xb050deafe0020434 0x158286f57f001021 0x9e81fe1ff1460c70 0x94f40ff0ff8a3063

def z1442 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xf3ff01f87f01fc1d 0xff9ff80fc3f80fe0

def z1443 : W := mkw 0xf017dfffe001281c 0x0780beffff000940 0xfffffffff0018c10 0x1fffffffff800c60

def z1444 : W := mkw 0xf010dfffe000001c 0x078086ffff000000 0xfef4fffff0000000 0x1ff7a7ffff800000

def z1445 : W := mkw 0x0680200014fc5281 0x6034010000a7e294 0x0000000002fe738f 0x600000000017f39c

def z1446 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xfeecff87fc01801c 0xf7f767fc3fe00c00

def z1447 : W := mkw 0x10400208b0224620 0x5082001045811231 0x88810619f1464c70 0x8c440830cf8a3263

def z1448 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x7e60fe07f080038e 0x73f307f03f84001c

def z1449 : W := mkw 0x0680200014fc5281 0x6034010000a7e294 0x0000000000fe0382 0x000000000007f01c

def z1450 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1e02fe0002fe0002 0x00f017f00017f000

def z1451 : W := mkw 0xfa17dfffeb14001f 0x07d0beffff58a000 0xfff7fffff37e0003 0xbfffbfffff9bf000

def z1452 : W := mkw 0x700743dda000000c 0x03803a1eed000000 0xfff7e7fff0000000 0x1fffbf3fff800000

def z1453 : W := mkw 0xb110deafe0008154 0x858886f57f00040a 0xfe08ff87f00183fc 0x17f047fc3f800c1f

def z1454 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfbb10679f1667e7f 0xbfdd8833cf8b33f3

def z1455 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfff7fffff3007c15 0xbfffbfffff9803e0

def z1456 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0800002 0x7fffbfffff840000

def z1457 : W := mkw 0x0540200014e2c760 0xd02a010000a7163b 0x000800000d67ce77 0xa0004000006b3e73

def z1458 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfef6ffe7f0000000 0x17f7b7ff3f800000

def z1459 : W := mkw 0x10400208b0224620 0x5082001045811231 0xfba1061ff1664fff 0xbfdd0830ff8b327f

def z1460 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x1f12fe67f0000000 0x18f897f33f800000

def z1461 : W := mkw 0xce07b5500fd4001b 0x06703daa807ea000 0xfff7fff80ffe700f 0xefffbfffc07ff380

def z1462 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xfffffffffe01b01c 0xfffffffffff00d80

def z1463 : W := mkw 0xb017deafe0000014 0x0580bef57f000000 0xbfe7fe1ff0000000 0x1dff3ff0ff800000

def z1464 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xffff1ff80ffffc1f 0xeffff8ffc07fffe0

def z1465 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0x9e8dff980dff8c12 0x84f46ffcc06ffc60

def z1466 : W := mkw 0x0080082250285280 0x6004004112814294 0xf7f619e672b8738f 0x7fbfb0cf3395c39c

def z1467 : W := mkw 0xce07b5500fd5281b 0x06703daa807ea940 0xbfefff980fffcc17 0xedff7ffcc07ffe60

def z1468 : W := mkw 0x480001500b01280a 0x0240000a80580940 0xe17a01f80f01fc1d 0xef0bd00fc0780fe0

def z1469 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0xfff3fe7ff0000000 0x1fff9ff3ff800000

def z1470 : W := mkw 0x15002208a4c08140 0x80a801104526040a 0xbba90619fcc183fe 0xfddd4830cfe60c1f

def z1471 : W := mkw 0x2080408510285284 0x6104020428814294 0xeee4e18782b8738f 0x7777270c3c15c39c

def z1472 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186672b8338a 0x5bbb90c33395c19c

def z1473 : W := mkw 0xf817dfffeb00001e 0x07c0beffff580000 0xfff7ffffffb80003 0xffffbffffffdc000

def z1474 : W := mkw 0xf117dfffe000815c 0x8788beffff00040a 0xfffffffff08183fe 0x7fffffffff840c1f

def z1475 : W := mkw 0x2500608504c08144 0x812803042826040a 0xeeece1878de783ff 0xf777670c3c6f3c1f

def z1476 : W := mkw 0x0080082240081080 0x2004004112004084 0x5552186672983188 0x4aaa90c33394c18c

def z1477 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0xffe7fe078ffe03ff 0xf7ff3ff03c7ff01f

def z1478 : W := mkw 0xf817dfffeb01281e 0x07c0beffff580940 0xffffffffff018c11 0xfffffffffff80c60

def z1479 : W := mkw 0xc80795500b01281a 0x06403caa80580940 0xfffffff80fb9fc1f 0xefffffffc07dcfe0

def z1480 : W := mkw 0x0080082250285280 0x6004004112814294 0xf772187e72b87f9f 0x7fbb90c3f395c3fc

def z1481 : W := mkw 0x2500608504c08144 0x812803042826040a 0x0e0ce1878cc183e2 0x1070670c3c660c1f

def z1482 : W := mkw 0x0080082250285280 0x6004004112814294 0x1512186672b87181 0x08a890c33395c38c

def z1483 : W := mkw 0x480701500b01280a 0x0240380a80580940 0xe05e01f80f01fc1d 0xef02f00fc0780fe0

def z1484 : W := mkw 0xf817d7ddab01281e 0x07c0bebeed580940 0xfbffe7f9ff01fc1d 0xffdfff3fcff80fe0

def z1485 : W := mkw 0x0e4020001ff64623 0x5072010000ffb231 0x000000000ffe4c03 0xe0000000007ff260

def z1486 : W := mkw 0x480701500b01280a 0x0240380a80580940 0x011f01f80f01fc01 0x0808f80fc0780fe0

def z1487 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfffffffffd01cc1d 0xffffffffffe80e60

def z1488 : W := mkw 0x0080082250285280 0x6004004112814294 0x7652186672b8738e 0x5bb290c33395c39c

def z1489 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0xa885e799f0000000 0x1d442f3ccf800000

def z1490 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0xfff7fffff0800188 0x5fffbfffff84000c

def z1491 : W := mkw 0xb010deafe0000014 0x058086f57f000000 0x5e52fe67f0000000 0x12f297f33f800000

def z1492 : W := mkw 0x0080082250285280 0x6004004112814294 0x5752186672b8738b 0x5aba90c33395c39c

def z1493 : W := mkw 0x0080082250285280 0x6004004112814294 0x7772186672f873ff 0xfbbb90c33397c39f

def z1494 : W := mkw 0x0d4020001fe3ef62 0xd06a010000ff1f7b 0x000800000fe7ffff 0xe0004000007f3fff

def z1495 : W := mkw 0x8e07b4000fd40013 0x04703da0007ea000 0x1fe7fe000ffe0277 0xe0ff3ff0007ff013

def z1496 : W := mkw 0xf017d7dda000001c 0x0780bebeed000000 0xffe5e79ff0000000 0x1fff2f3cff800000

def z1497 : W := mkw 0x10400208b0224620 0x5082001045811231 0xbbe30619f3664e77 0xfddf1830cf9b3273

def z1498 : W := mkw 0xf097dfffe008109c 0x2784beffff004084 0xfff7fffff298718d 0x7fffbfffff94c38c

def z1499 : W := mkw 0x10400208b0224620 0x5082001045811231 0x1ba10619f1664e63 0xb8dd0830cf8b3273

def z1500 : W := mkw 0x2500608504c08144 0x812803042826040a 0xefece1878cc1c3ff 0xff7f670c3c660e1f

def z1501 : W := mkw 0xf017dfffe000001c 0x0780beffff000000 0x9f97fffff0000000 0x1cfcbfffff800000

def z1502 : W := mkw 0xce07b5500fd4001b 0x06703daa807ea000 0x5ff7ffe00ffe0003 0xe2ffbfff007ff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z8,z9,z6]),(0,[z10,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z11,z4,z9,z12]),(0,[z1,z2,z13,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z15,z9,z6]),(0,[z1,z2,z3,z4,z16,z17,z6]),(0,[z1,z2,z3,z18,z4,z9,z19]),(0,[z1,z2,z20,z3,z4,z9,z19]),(0,[z1,z21,z2,z3,z4,z9,z12])],[(0,[z22,z1,z2,z3,z4,z9,z6]),(0,[z23,z1,z2,z3,z4,z17,z6])],[(0,[z1,z24,z25,z3,z4,z9,z6]),(0,[z26,z1,z2,z3,z4,z9,z6]),(0,[z27,z1,z2,z3,z4,z9,z6]),(0,[z28,z1,z29,z2,z3,z4,z9]),(0,[z1,z2,z30,z3,z4,z9,z19]),(0,[z1,z2,z3,z31,z4,z14,z6]),(0,[z1,z2,z3,z32,z4,z9,z33]),(0,[z1,z2,z3,z18,z4,z17,z6])],[(0,[z1,z34,z2,z3,z4,z9,z6]),(0,[z27,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z35,z36,z9,z6]),(0,[z28,z1,z37,z2,z3,z4,z9]),(0,[z1,z25,z3,z31,z4,z9,z6]),(0,[z1,z38,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z39,z6]),(1,[z1,z2,z3,z4,z9,z40])],[(0,[z1,z2,z41,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z42,z43]),(0,[z1,z2,z30,z3,z4,z17,z6])],[(0,[z1,z2,z3,z4,z44,z9,z6]),(0,[z45,z1,z2,z3,z4,z9,z12]),(0,[z1,z46,z2,z3,z4,z9,z6]),(0,[z47,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z17,z14,z6]),(0,[z1,z2,z48,z3,z4,z17,z6])],[(0,[z0,z1,z2,z7,z4,z9,z6]),(0,[z49,z2,z7,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z50,z9,z6]),(0,[z1,z2,z3,z4,z51,z9,z6]),(0,[z1,z2,z3,z52,z4,z9,z6])],[(0,[z53,z1,z2,z3,z4,z9,z6]),(0,[z1,z54,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z55,z14,z6]),(0,[z56,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z57,z1,z2,z3,z4,z9,z6]),(1,[z1,z58,z2,z3,z4,z9]),(0,[z59,z1,z2,z3,z4,z9,z6]),(0,[z1,z60,z2,z3,z4,z9,z6]),(0,[z1,z61,z2,z3,z4,z17,z6])],[(0,[z1,z2,z7,z3,z4,z9,z12]),(0,[z1,z2,z3,z62,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z43,z63]),(0,[z1,z2,z3,z4,z64,z9,z6]),(0,[z1,z2,z3,z4,z65,z9,z6])],[(0,[z1,z2,z3,z4,z66,z9,z6]),(0,[z1,z2,z3,z4,z9,z67,z6]),(0,[z68,z1,z2,z3,z4,z9,z43]),(0,[z1,z2,z3,z4,z69,z9,z6]),(0,[z70,z71,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z72,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z73]),(0,[z1,z74,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z14,z6,z75]),(0,[z1,z76,z2,z3,z4,z9,z6])],[(0,[z1,z2,z77,z4,z8,z9,z6]),(0,[z1,z2,z3,z4,z78,z9,z6]),(1,[z1,z79,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z80,z9,z6])],[(0,[z1,z2,z3,z4,z9,z81,z6]),(0,[z1,z2,z3,z4,z9,z82,z19]),(0,[z1,z2,z83,z3,z4,z9,z63]),(0,[z1,z2,z3,z4,z17,z6,z19]),(0,[z1,z2,z3,z84,z4,z9,z6])],[(1,[z1,z85,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z86,z9,z6]),(0,[z28,z1,z2,z3,z4,z9,z81]),(0,[z1,z2,z87,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z81,z19]),(0,[z1,z2,z3,z4,z9,z88,z6])],[(0,[z89,z1,z2,z3,z4,z9,z6]),(0,[z90,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z91,z4,z9,z6]),(0,[z1,z2,z3,z4,z14,z42,z6]),(1,[z1,z2,z3,z92,z9,z6])],[(0,[z27,z1,z2,z93,z4,z9,z6]),(1,[z71,z2,z3,z4,z9,z6]),(0,[z1,z94,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z6,z95]),(0,[z28,z1,z2,z3,z4,z96,z9]),(0,[z1,z2,z3,z4,z97,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z98]),(0,[z1,z2,z3,z4,z99,z9,z6]),(0,[z1,z2,z3,z32,z4,z100,z6]),(0,[z1,z2,z3,z4,z101,z9,z6]),(0,[z1,z2,z3,z35,z4,z17,z6])],[(0,[z102,z1,z2,z3,z4,z9,z6])],[(1,[z1,z2,z3,z4,z88,z6]),(0,[z1,z29,z2,z3,z4,z9,z103]),(0,[z1,z2,z3,z4,z104,z17,z6]),(0,[z1,z105,z2,z3,z4,z9,z19])],[(0,[z1,z2,z3,z4,z9,z106,z6]),(0,[z107,z2,z3,z36,z4,z9,z6]),(0,[z108,z1,z2,z109,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z9,z6]),(0,[z70,z1,z2,z13,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z110,z6]),(0,[z1,z111,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z112,z6])],[(0,[z113,z1,z2,z3,z4,z9,z6]),(0,[z107,z1,z2,z3,z4,z9,z6]),(0,[z114,z1,z2,z3,z4,z17,z6]),(1,[z1,z2,z3,z115,z4,z9]),(0,[z1,z2,z3,z4,z9,z116,z6]),(0,[z1,z2,z3,z4,z9,z117,z6]),(0,[z1,z2,z3,z4,z9,z6,z118]),(0,[z70,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z119,z6]),(0,[z1,z29,z2,z3,z4,z14,z6])],[(0,[z107,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z120,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z121,z6]),(1,[z1,z2,z3,z4,z9,z122]),(0,[z23,z1,z2,z3,z31,z9,z6]),(0,[z45,z1,z123,z3,z4,z9,z6]),(0,[z1,z2,z3,z124,z4,z9,z6])],[(1,[z125,z126,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z127]),(0,[z45,z1,z2,z3,z4,z9,z128]),(1,[z129,z2,z3,z4,z9,z6]),(0,[z70,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z130,z9,z6]),(0,[z1,z2,z3,z4,z14,z131,z6]),(0,[z132,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z133,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z134,z6])],[(0,[z125,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z7,z4,z9,z82,z6]),(0,[z28,z1,z2,z3,z4,z9,z19]),(0,[z10,z1,z2,z3,z4,z9,z135]),(1,[z136,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z137,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z138,z6]),(0,[z1,z123,z2,z3,z4,z9,z12]),(0,[z1,z2,z139,z3,z4,z9,z6]),(0,[z1,z2,z3,z140,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z103]),(0,[z1,z141,z2,z3,z4,z9,z6])]],
   [[(1,[z1,z2,z3,z4,z9,z6]),(0,[z27,z1,z34,z3,z4,z9,z6]),(1,[z1,z2,z3,z142,z14,z6]),(0,[z10,z1,z2,z3,z4,z9,z43]),(0,[z1,z2,z3,z143,z4,z9,z6]),(0,[z1,z141,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z12,z144])],[(0,[z1,z2,z3,z145,z4,z9,z6]),(0,[z1,z2,z3,z36,z4,z9,z6]),(0,[z1,z2,z146,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z147,z6]),(0,[z1,z2,z83,z4,z9,z6,z103]),(0,[z1,z2,z3,z18,z4,z148,z6]),(1,[z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z149,z3,z4,z9,z6])],[(0,[z1,z2,z3,z36,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z6,z150]),(0,[z1,z2,z3,z4,z151,z9,z6]),(0,[z68,z1,z2,z3,z4,z9,z12]),(0,[z152,z1,z2,z3,z4,z9,z6])],[(0,[z153,z24,z2,z3,z4,z9,z6]),(0,[z2,z7,z3,z77,z4,z9,z6]),(0,[z154,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z155,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z156,z12]),(0,[z1,z2,z3,z4,z157,z9,z158])],[(0,[z1,z24,z60,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z159]),(0,[z1,z2,z3,z142,z9,z14,z6]),(0,[z1,z2,z3,z4,z55,z82,z6]),(0,[z160,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z138,z6]),(1,[z1,z46,z3,z4,z9,z135]),(0,[z1,z46,z2,z3,z4,z9,z135]),(0,[z161,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z162,z6]),(0,[z1,z2,z3,z4,z163,z17,z6]),(0,[z1,z164,z2,z3,z4,z9,z12])],[(0,[z1,z165,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z4,z17,z6]),(0,[z45,z1,z2,z3,z166,z9,z6]),(0,[z70,z1,z167,z3,z4,z9,z6]),(0,[z1,z2,z13,z3,z4,z9,z6]),(0,[z1,z2,z168,z3,z4,z157,z6]),(0,[z1,z2,z3,z4,z9,z6,z169]),(0,[z1,z170,z2,z3,z4,z9,z6])],[(1,[z1,z54,z3,z4,z9,z6]),(0,[z1,z2,z13,z3,z4,z9,z19]),(0,[z1,z171,z2,z3,z4,z9,z6])],[(0,[z108,z1,z2,z3,z4,z172,z6]),(0,[z1,z2,z3,z31,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z173]),(0,[z70,z1,z2,z3,z35,z9,z6]),(0,[z1,z2,z3,z4,z17,z174,z6])]],
   [[(0,[z107,z2,z3,z77,z4,z9,z6]),(0,[z1,z175,z2,z3,z11,z4,z9]),(0,[z1,z2,z30,z4,z8,z9,z6]),(0,[z1,z2,z3,z4,z96,z157,z6]),(0,[z1,z74,z2,z3,z4,z9,z176])],[(0,[z1,z2,z3,z4,z9,z177,z6]),(0,[z1,z2,z3,z4,z9,z178,z6]),(1,[z1,z2,z3,z4,z12,z14]),(0,[z1,z2,z3,z18,z9,z6,z19])],[(0,[z1,z2,z3,z4,z9,z6,z179]),(0,[z49,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z180,z6]),(0,[z108,z1,z2,z3,z4,z9,z181]),(0,[z182,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z183,z9,z6]),(1,[z1,z167,z3,z4,z9,z6]),(0,[z184,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z14,z6,z19])],[(0,[z1,z2,z3,z4,z142,z9,z12]),(0,[z1,z2,z3,z4,z172,z14,z6]),(0,[z1,z2,z3,z4,z17,z6,z43])],[(0,[z1,z2,z185,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z42,z186]),(0,[z1,z2,z3,z35,z31,z9,z6]),(0,[z187,z1,z2,z3,z4,z9,z6])],[(0,[z125,z2,z126,z3,z4,z9,z6]),(1,[z1,z2,z93,z4,z9,z6]),(1,[z45,z1,z3,z4,z156,z6]),(1,[z1,z2,z3,z4,z9,z188])],[(0,[z1,z2,z3,z189,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z190]),(0,[z23,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z6,z191]),(1,[z68,z1,z3,z4,z9,z81]),(0,[z1,z2,z13,z32,z4,z9,z6]),(0,[z192,z1,z2,z3,z4,z9,z6])],[(0,[z193,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z77,z4,z9,z19]),(0,[z194,z1,z2,z3,z4,z9,z6]),(0,[z108,z2,z3,z4,z9,z55,z6]),(0,[z195,z1,z2,z30,z4,z9,z6]),(0,[z1,z2,z3,z4,z196,z9,z6]),(0,[z1,z2,z3,z18,z4,z9,z12]),(0,[z1,z2,z197,z3,z4,z9,z6])]],
   [[(0,[z153,z1,z2,z3,z4,z14,z6]),(0,[z1,z24,z123,z3,z4,z9,z6]),(0,[z0,z1,z2,z77,z4,z9,z6]),(0,[z1,z2,z3,z198,z4,z9,z6]),(0,[z1,z199,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z200,z6])],[(0,[z1,z60,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z77,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z201,z6]),(0,[z1,z2,z30,z3,z4,z9,z12]),(0,[z1,z25,z2,z3,z202,z9,z6])],[(0,[z203,z1,z2,z3,z4,z9,z6]),(0,[z1,z204,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z205])],[(0,[z206,z1,z2,z3,z4,z9,z6]),(0,[z207,z1,z2,z3,z4,z9,z6])],[(0,[z0,z49,z2,z3,z4,z9,z6]),(0,[z2,z3,z77,z4,z142,z9,z6])],[(1,[z1,z2,z3,z208,z9,z6]),(0,[z1,z2,z3,z4,z9,z209,z6]),(0,[z1,z61,z2,z3,z4,z9,z12]),(0,[z1,z2,z210,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z211,z6])],[(0,[z1,z2,z3,z212,z4,z9,z6]),(0,[z1,z2,z3,z4,z213,z9,z6]),(1,[z1,z34,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z214,z6]),(0,[z108,z1,z2,z3,z4,z55,z6]),(0,[z28,z1,z2,z3,z4,z9,z43]),(0,[z1,z2,z3,z215,z4,z9,z6]),(0,[z23,z216,z2,z3,z4,z9,z6])],[(0,[z1,z126,z3,z4,z9,z81,z6]),(1,[z195,z1,z11,z4,z9,z6]),(0,[z1,z2,z168,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z217,z9,z6]),(0,[z1,z29,z2,z3,z4,z9,z63]),(0,[z1,z2,z3,z35,z9,z6,z19])]],
   [[(0,[z10,z1,z37,z2,z3,z4,z9]),(0,[z195,z218,z2,z3,z4,z9,z6]),(0,[z219,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z3,z4,z9,z19]),(0,[z220,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z221,z9,z6])],[(0,[z125,z153,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z222]),(0,[z1,z223,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z224]),(0,[z1,z29,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z225,z9,z6])],[(0,[z153,z1,z2,z3,z4,z9,z226]),(0,[z1,z2,z3,z4,z227,z9,z6]),(0,[z1,z2,z168,z11,z4,z9,z6]),(0,[z1,z2,z3,z4,z228,z9,z6]),(0,[z229,z1,z2,z3,z4,z9,z6]),(0,[z1,z25,z2,z3,z4,z9,z19]),(0,[z70,z1,z2,z4,z8,z9,z6]),(0,[z1,z2,z3,z4,z230,z9,z6]),(0,[z1,z74,z2,z3,z4,z9,z231]),(1,[z1,z2,z3,z4,z148,z6])],[(0,[z232,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z233,z6]),(0,[z1,z2,z3,z4,z202,z14,z6]),(0,[z1,z2,z3,z31,z4,z234,z6]),(0,[z68,z1,z2,z83,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z82,z12]),(0,[z1,z2,z3,z4,z96,z9,z19])],[(1,[z1,z2,z3,z36,z14,z6]),(0,[z1,z2,z3,z4,z235,z9,z6]),(1,[z1,z2,z236,z4,z9,z6]),(0,[z1,z2,z3,z237,z4,z9,z6]),(0,[z1,z2,z83,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z6,z63])],[(0,[z23,z1,z2,z238,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z239]),(0,[z1,z2,z3,z4,z9,z12,z63])],[(0,[z2,z126,z3,z4,z9,z55,z6]),(0,[z1,z24,z2,z3,z4,z17,z6]),(0,[z2,z3,z4,z172,z9,z55,z6]),(0,[z1,z2,z3,z4,z9,z135,z103])],[(0,[z114,z2,z3,z4,z172,z9,z6]),(1,[z1,z2,z3,z4,z9,z240]),(0,[z1,z2,z30,z4,z9,z82,z6]),(1,[z1,z2,z3,z241,z9,z6]),(0,[z45,z1,z2,z3,z4,z156,z6]),(0,[z1,z2,z3,z4,z9,z12,z6])]],
   [[(0,[z1,z24,z3,z11,z4,z9,z6]),(0,[z1,z2,z3,z242,z4,z9,z6]),(0,[z1,z2,z3,z4,z243,z9,z6]),(0,[z1,z2,z3,z4,z9,z244,z6]),(0,[z245,z1,z2,z3,z4,z9,z6])],[(0,[z246,z1,z2,z3,z4,z9,z6]),(0,[z247,z1,z2,z3,z4,z9,z6]),(0,[z248,z1,z2,z3,z4,z9,z6]),(0,[z114,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z14,z6,z43]),(0,[z1,z2,z249,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z250,z6]),(0,[z161,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z251]),(0,[z252,z1,z2,z3,z4,z9,z6]),(0,[z1,z253,z2,z3,z4,z9,z6]),(0,[z254,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z8,z17,z6])],[(1,[z1,z2,z3,z4,z9,z255]),(1,[z1,z2,z3,z4,z9,z256]),(0,[z1,z2,z3,z4,z257,z9,z6]),(0,[z70,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z32,z4,z14,z6]),(0,[z1,z61,z2,z4,z9,z82,z6]),(0,[z1,z258,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z9,z12,z19]),(0,[z1,z2,z259,z3,z4,z9,z6])],[(0,[z260,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z3,z4,z9,z188]),(0,[z1,z2,z3,z4,z9,z261,z6]),(2,[z1,z2,z3,z14,z19]),(0,[z262,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z263]),(0,[z108,z1,z85,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z55,z19]),(0,[z1,z2,z264,z3,z4,z9,z6]),(0,[z10,z1,z2,z3,z4,z96,z9]),(0,[z265,z1,z2,z3,z4,z9,z6])],[(0,[z28,z1,z2,z3,z4,z9,z12]),(1,[z23,z1,z3,z202,z9,z6]),(0,[z1,z2,z3,z266,z4,z9,z6]),(1,[z1,z2,z168,z4,z157,z6])],[(0,[z49,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z186,z6]),(0,[z1,z2,z3,z4,z267,z9,z6]),(0,[z1,z46,z2,z3,z4,z9,z81]),(0,[z1,z2,z3,z92,z96,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z172,z9,z6]),(0,[z1,z2,z79,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z268]),(1,[z1,z2,z3,z4,z9,z231]),(0,[z1,z2,z3,z4,z211,z14,z6]),(0,[z1,z2,z3,z4,z269,z17,z6]),(0,[z270,z1,z2,z3,z4,z9,z19]),(0,[z1,z271,z2,z3,z4,z9,z12])],[(0,[z272,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z273,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z32,z4,z274,z6])],[(0,[z1,z2,z3,z4,z9,z275,z6]),(0,[z1,z276,z2,z3,z4,z9,z6]),(0,[z28,z10,z2,z3,z4,z9,z6]),(1,[z277,z2,z3,z4,z9,z6]),(0,[z1,z46,z2,z3,z4,z96,z9]),(0,[z1,z2,z32,z4,z8,z9,z6]),(1,[z1,z2,z3,z4,z9,z158]),(0,[z270,z1,z2,z3,z4,z17,z6]),(0,[z1,z278,z2,z3,z4,z9,z19]),(0,[z1,z141,z2,z3,z4,z279,z6])],[(0,[z1,z2,z3,z280,z4,z9,z6]),(0,[z1,z2,z3,z4,z234,z9,z6]),(1,[z1,z2,z3,z4,z279,z6])],[(0,[z10,z1,z2,z3,z4,z9,z19]),(0,[z1,z281,z2,z3,z4,z9,z6]),(0,[z1,z282,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z283,z6]),(0,[z1,z278,z2,z3,z4,z17,z6])],[(0,[z153,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z284,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z156,z82,z6]),(0,[z1,z2,z3,z4,z17,z14,z6])],[(0,[z10,z1,z2,z3,z4,z17,z6]),(0,[z1,z285,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z286,z4,z9,z6]),(0,[z1,z2,z3,z4,z104,z9,z186]),(0,[z1,z2,z287,z3,z4,z9,z6])]],
   [[(0,[z288,z1,z2,z3,z4,z9,z6]),(0,[z27,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z289,z6]),(0,[z108,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z55,z6]),(0,[z290,z1,z2,z3,z4,z9,z6]),(0,[z1,z46,z3,z4,z9,z6,z135]),(1,[z1,z2,z3,z9,z291,z6])],[(0,[z292,z1,z2,z3,z4,z9,z6]),(0,[z1,z293,z2,z3,z4,z9,z6]),(1,[z1,z294,z3,z4,z9,z6]),(0,[z108,z1,z2,z3,z4,z9,z19]),(0,[z1,z123,z2,z3,z4,z156,z6]),(0,[z1,z46,z2,z3,z4,z9,z19]),(0,[z1,z37,z2,z3,z4,z9,z103])],[(0,[z0,z1,z2,z3,z189,z9,z6]),(0,[z218,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z228,z6]),(0,[z1,z2,z210,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z144,z6])],[(0,[z1,z2,z3,z295,z4,z9,z6]),(0,[z1,z2,z3,z296,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z297,z6]),(0,[z1,z37,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z298,z12]),(0,[z1,z299,z2,z3,z4,z9,z6])],[(0,[z0,z1,z2,z3,z4,z9,z222]),(0,[z1,z2,z13,z7,z4,z9,z6]),(1,[z27,z2,z3,z142,z9,z6]),(0,[z1,z60,z2,z3,z4,z9,z19]),(0,[z300,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z3,z4,z9,z239])],[(0,[z1,z2,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z289,z6]),(0,[z1,z2,z301,z3,z4,z9,z6])],[(0,[z302,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z77,z4,z9,z12]),(0,[z1,z303,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z36,z4,z289,z6]),(0,[z1,z304,z2,z3,z4,z9,z6]),(0,[z1,z60,z2,z11,z4,z9,z6]),(0,[z1,z60,z3,z4,z202,z9,z6]),(0,[z1,z60,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z12,z135]),(0,[z1,z74,z2,z3,z4,z9,z19])],[(0,[z1,z2,z3,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z305,z9,z6]),(0,[z1,z2,z3,z4,z9,z43,z19]),(0,[z306,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z307,z9,z6]),(0,[z1,z2,z3,z4,z9,z308,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z6,z309]),(0,[z1,z2,z3,z4,z202,z9,z6]),(0,[z1,z2,z3,z202,z8,z9,z6]),(0,[z45,z1,z2,z310,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z157,z6]),(0,[z1,z74,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z311,z9,z6])],[(0,[z1,z2,z126,z3,z4,z14,z6]),(0,[z153,z2,z3,z77,z4,z9,z6]),(1,[z0,z2,z77,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z128]),(0,[z1,z123,z3,z4,z312,z9,z6]),(0,[z68,z313,z2,z3,z4,z9,z6]),(0,[z1,z2,z83,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z314,z9,z6])],[(0,[z1,z25,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z315,z6]),(0,[z23,z1,z2,z3,z4,z9,z98]),(0,[z1,z2,z3,z4,z316,z9,z6]),(0,[z1,z2,z3,z202,z9,z14,z6]),(0,[z1,z317,z2,z3,z4,z9,z6]),(0,[z318,z1,z2,z3,z4,z9,z6]),(0,[z1,z319,z2,z3,z4,z9,z6])],[(0,[z1,z24,z3,z4,z9,z156,z6]),(0,[z1,z2,z320,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z135,z63]),(0,[z1,z2,z3,z4,z321,z9,z6]),(0,[z1,z2,z3,z4,z9,z322,z6]),(0,[z1,z2,z3,z4,z96,z6,z63])],[(0,[z1,z2,z3,z4,z323,z9,z6]),(0,[z324,z1,z2,z3,z4,z9,z6]),(1,[z1,z325,z2,z3,z4,z9]),(0,[z1,z2,z3,z326,z4,z9,z6])],[(0,[z1,z2,z327,z3,z4,z9,z6]),(0,[z328,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z31,z14,z6]),(0,[z329,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z4,z157,z9,z82,z6]),(0,[z1,z330,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z19,z331]),(0,[z1,z332,z2,z3,z4,z9,z6])],[(0,[z1,z24,z2,z3,z4,z9,z179]),(0,[z27,z1,z2,z3,z4,z9,z95]),(0,[z1,z333,z2,z3,z4,z9,z6]),(0,[z334,z1,z2,z3,z4,z9,z6]),(0,[z68,z335,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z336]),(0,[z1,z29,z2,z3,z4,z244,z6])],[(0,[z28,z1,z2,z83,z3,z4,z9]),(0,[z23,z1,z2,z3,z4,z337,z6]),(0,[z1,z2,z167,z3,z4,z9,z6]),(0,[z1,z338,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z4,z9,z6]),(0,[z1,z2,z3,z4,z142,z14,z6]),(0,[z1,z2,z3,z4,z9,z339,z6]),(1,[z1,z2,z3,z166,z9,z6]),(0,[z1,z2,z3,z32,z4,z9,z6]),(0,[z1,z2,z3,z4,z340,z9,z6]),(0,[z1,z2,z3,z341,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z342,z6]),(0,[z195,z1,z2,z3,z4,z14,z6]),(1,[z1,z2,z343,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z344,z6]),(0,[z345,z1,z2,z3,z4,z9,z6]),(0,[z1,z74,z2,z3,z35,z9,z6]),(0,[z1,z2,z3,z4,z4,z9,z19])],[(0,[z346,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z347,z9,z6]),(0,[z107,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z348,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z349]),(0,[z1,z2,z3,z4,z9,z350,z6]),(0,[z1,z2,z3,z4,z17,z82,z6])],[(0,[z1,z24,z2,z3,z4,z9,z12]),(0,[z23,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z17,z81,z6]),(1,[z1,z2,z3,z4,z9,z322]),(0,[z1,z2,z3,z4,z14,z14,z6]),(1,[z1,z2,z3,z4,z9,z162])],[(0,[z1,z2,z3,z4,z9,z351,z6]),(0,[z1,z2,z3,z93,z4,z9,z6]),(0,[z28,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z157,z9,z12]),(0,[z1,z2,z3,z4,z14,z352,z6])],[(0,[z1,z2,z353,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z354,z6]),(0,[z1,z60,z25,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z312,z9,z12]),(0,[z1,z141,z2,z3,z4,z17,z6])],[(0,[z1,z46,z24,z3,z4,z9,z6]),(0,[z355,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z7,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z356,z6]),(0,[z1,z2,z3,z357,z4,z9,z6]),(0,[z1,z2,z3,z4,z358,z9,z6]),(1,[z1,z2,z3,z4,z17,z6])],[(0,[z1,z2,z3,z36,z4,z17,z6]),(0,[z1,z2,z3,z4,z359,z9,z6]),(0,[z1,z2,z3,z360,z4,z9,z6]),(0,[z1,z2,z3,z4,z8,z9,z12]),(0,[z1,z29,z2,z3,z4,z39,z6]),(0,[z1,z2,z3,z4,z9,z12,z14]),(1,[z1,z2,z3,z4,z17,z19]),(0,[z1,z2,z3,z4,z9,z361,z6])]],
   [[(0,[z1,z2,z3,z4,z362,z9,z6]),(0,[z1,z2,z3,z363,z4,z9,z6]),(0,[z1,z2,z3,z364,z4,z9,z6]),(0,[z1,z46,z2,z3,z4,z9,z43]),(0,[z1,z2,z3,z365,z157,z9,z6])],[(0,[z1,z2,z3,z4,z9,z366,z6]),(0,[z367,z1,z2,z3,z4,z9,z6]),(1,[z1,z123,z3,z4,z312,z6]),(0,[z1,z2,z3,z4,z96,z9,z42]),(0,[z1,z2,z3,z4,z9,z6,z368])],[(0,[z27,z1,z2,z3,z142,z9,z6]),(0,[z1,z2,z3,z369,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z9,z6]),(0,[z1,z2,z3,z4,z9,z370,z6]),(0,[z1,z2,z3,z4,z9,z6,z75])],[(0,[z371,z1,z2,z3,z4,z9,z6]),(0,[z2,z126,z3,z77,z4,z9,z6]),(0,[z372,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z13,z11,z4,z9,z6]),(0,[z1,z2,z3,z31,z4,z9,z19]),(0,[z1,z2,z13,z3,z4,z17,z6])],[(0,[z1,z2,z373,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z55,z12]),(0,[z1,z2,z3,z115,z4,z9,z6])],[(0,[z114,z2,z126,z3,z4,z9,z6]),(0,[z374,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z31,z4,z17,z6]),(0,[z45,z375,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z92,z4,z9,z6])],[(0,[z153,z1,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z226]),(0,[z376,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z31,z4,z138,z6]),(0,[z1,z141,z2,z3,z35,z9,z6]),(0,[z1,z37,z2,z3,z4,z9,z63])],[(0,[z1,z2,z3,z4,z377,z9,z6]),(0,[z153,z2,z3,z4,z9,z55,z6]),(0,[z378,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z379]),(0,[z270,z1,z2,z3,z4,z9,z12])]],
   [[(0,[z107,z2,z126,z3,z4,z9,z6]),(0,[z153,z1,z2,z3,z4,z9,z255]),(0,[z132,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z380,z4,z9,z6]),(0,[z10,z2,z3,z4,z9,z186,z6]),(0,[z45,z1,z2,z3,z4,z312,z6]),(0,[z1,z2,z3,z4,z9,z381,z6]),(0,[z1,z2,z3,z4,z183,z17,z6]),(0,[z1,z37,z2,z3,z4,z96,z6]),(0,[z1,z37,z2,z3,z4,z9,z6])],[(0,[z1,z46,z126,z3,z4,z9,z6])],[(0,[z28,z2,z126,z3,z4,z9,z6]),(0,[z1,z2,z343,z3,z4,z9,z6]),(0,[z1,z382,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z4,z14,z6])],[(0,[z27,z107,z2,z3,z4,z9,z6]),(0,[z108,z1,z2,z3,z4,z9,z256]),(0,[z10,z1,z2,z3,z4,z9,z12]),(0,[z1,z383,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z236,z4,z9,z6]),(0,[z1,z2,z3,z4,z384,z9,z6]),(0,[z1,z385,z2,z3,z4,z9,z6]),(0,[z386,z1,z2,z3,z4,z9,z6]),(0,[z1,z387,z2,z3,z4,z9,z6])],[(0,[z1,z24,z3,z4,z9,z81,z6]),(1,[z1,z2,z3,z4,z9,z95]),(0,[z1,z2,z3,z4,z388,z9,z6]),(0,[z70,z1,z2,z3,z8,z9,z6]),(0,[z1,z2,z13,z3,z35,z9,z6]),(0,[z1,z2,z3,z4,z104,z14,z6]),(0,[z389,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z279,z9,z6])],[(0,[z27,z1,z2,z3,z4,z390,z6]),(0,[z27,z1,z2,z3,z4,z9,z12]),(0,[z68,z1,z2,z3,z4,z9,z186]),(0,[z1,z2,z3,z4,z391,z14,z6])],[(0,[z1,z2,z126,z3,z4,z9,z6]),(0,[z49,z1,z2,z7,z4,z9,z6]),(1,[z1,z392,z2,z3,z4,z9]),(0,[z114,z1,z2,z3,z4,z14,z6]),(0,[z68,z1,z3,z4,z9,z81,z6]),(0,[z70,z1,z2,z3,z9,z14,z6]),(0,[z1,z393,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z394,z17,z6]),(0,[z395,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z396,z9,z6]),(0,[z1,z397,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z370,z14,z6])]],
   [[(0,[z1,z398,z2,z3,z4,z9,z6]),(0,[z313,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z148,z6]),(1,[z1,z37,z2,z3,z4,z104])],[(0,[z125,z1,z2,z3,z4,z14,z6]),(0,[z27,z1,z2,z3,z4,z399,z6]),(0,[z195,z1,z2,z3,z97,z9,z6]),(0,[z1,z2,z400,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z401]),(0,[z1,z2,z310,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z14,z81,z6]),(0,[z1,z2,z3,z4,z9,z12,z81])],[(0,[z1,z2,z3,z4,z9,z6,z402]),(0,[z1,z330,z2,z3,z4,z9,z6]),(1,[z70,z1,z2,z8,z9,z6]),(0,[z1,z2,z3,z4,z403,z9,z6])],[(0,[z195,z1,z2,z3,z4,z9,z122]),(0,[z1,z60,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z156,z14,z6]),(0,[z1,z2,z3,z4,z17,z312,z6]),(0,[z1,z2,z3,z4,z82,z14,z6])],[(0,[z1,z2,z373,z3,z77,z4,z9]),(0,[z1,z2,z404,z3,z4,z9,z6]),(0,[z107,z1,z2,z3,z142,z9,z6]),(0,[z1,z2,z3,z4,z9,z12,z405])],[(0,[z406,z1,z2,z3,z4,z9,z6]),(0,[z195,z136,z2,z3,z4,z9,z6]),(0,[z407,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z3,z4,z17,z6]),(0,[z1,z29,z2,z3,z4,z9,z19]),(0,[z1,z74,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z200,z14,z6])],[(0,[z28,z153,z2,z3,z4,z9,z6]),(0,[z408,z1,z2,z3,z4,z9,z6]),(0,[z195,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z409,z6]),(0,[z219,z1,z2,z3,z4,z17,z6])],[(0,[z0,z1,z2,z3,z4,z14,z6]),(0,[z1,z85,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z410,z4,z9,z6]),(0,[z195,z1,z2,z3,z4,z9,z19]),(0,[z1,z25,z2,z3,z4,z17,z6]),(1,[z313,z2,z3,z4,z9,z6]),(0,[z1,z61,z2,z3,z4,z82,z6]),(0,[z1,z2,z3,z4,z104,z157,z6])]],
   [[(0,[z1,z2,z3,z11,z4,z14,z6]),(0,[z1,z2,z3,z31,z4,z9,z401]),(0,[z1,z411,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z96,z17,z6]),(0,[z1,z2,z3,z4,z9,z12,z361])],[(0,[z108,z1,z294,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z6]),(0,[z1,z25,z3,z11,z4,z9,z6]),(0,[z1,z60,z30,z3,z4,z9,z6]),(0,[z1,z2,z3,z412,z4,z9,z6]),(0,[z1,z29,z2,z83,z4,z9,z6]),(0,[z232,z1,z2,z3,z4,z17,z6]),(0,[z1,z141,z2,z3,z18,z9,z6])],[(0,[z1,z413,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z414,z4,z9,z6])],[(0,[z415,z1,z2,z3,z4,z9,z6]),(0,[z1,z416,z2,z3,z4,z9,z6]),(0,[z1,z2,z417,z3,z4,z9,z6]),(0,[z10,z1,z2,z3,z4,z9,z186]),(0,[z1,z3,z11,z4,z202,z9,z6]),(1,[z1,z175,z2,z3,z4,z9]),(1,[z1,z2,z3,z18,z9,z19]),(0,[z1,z2,z3,z4,z9,z12,z19])],[(0,[z1,z2,z3,z4,z17,z172,z6]),(1,[z335,z2,z3,z4,z9,z6])],[(0,[z45,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z6,z418]),(0,[z1,z2,z3,z4,z9,z419,z6]),(0,[z420,z1,z2,z3,z4,z14,z6])],[(1,[z1,z2,z3,z4,z9,z179]),(0,[z27,z1,z2,z3,z36,z9,z6]),(0,[z1,z2,z3,z4,z9,z390,z6]),(0,[z1,z2,z294,z3,z4,z9,z6]),(0,[z1,z335,z2,z3,z4,z9,z6]),(0,[z421,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z5,z6]),(0,[z107,z1,z2,z3,z4,z9,z12]),(1,[z1,z2,z3,z4,z9,z33]),(0,[z422,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z168,z77,z4,z9,z6]),(1,[z1,z2,z3,z423,z9,z6]),(1,[z1,z74,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z9,z424,z6])],[(0,[z425,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z7,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z6,z426]),(0,[z1,z392,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z427,z6]),(0,[z1,z2,z3,z4,z428,z9,z6]),(0,[z1,z429,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z104,z82,z6]),(0,[z1,z2,z3,z4,z9,z112,z6]),(0,[z1,z2,z3,z4,z430,z9,z6])],[(0,[z1,z431,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z191]),(0,[z1,z141,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z432,z4,z9,z6])],[(0,[z49,z1,z2,z3,z4,z9,z19]),(1,[z1,z2,z3,z4,z390,z6]),(0,[z1,z433,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z186,z19]),(0,[z1,z2,z3,z4,z434,z9,z6]),(0,[z1,z2,z3,z4,z9,z435,z6]),(1,[z1,z2,z3,z4,z9,z12])],[(0,[z436,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z2,z3,z4,z437,z6]),(0,[z1,z2,z3,z36,z4,z9,z12]),(0,[z1,z2,z3,z4,z172,z9,z19]),(1,[z28,z2,z3,z4,z9,z43]),(0,[z10,z1,z2,z83,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z6,z438])],[(0,[z49,z1,z2,z3,z4,z17,z6]),(0,[z439,z1,z2,z3,z4,z9,z6]),(0,[z440,z1,z2,z3,z4,z9,z6]),(1,[z70,z1,z2,z3,z14,z6])],[(1,[z108,z2,z3,z4,z55,z6]),(0,[z1,z2,z3,z4,z9,z6,z188])],[(0,[z1,z2,z3,z441,z4,z9,z6]),(1,[z1,z2,z3,z4,z399,z6]),(0,[z1,z442,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z443,z4,z9,z6]),(0,[z1,z2,z13,z3,z4,z9,z12]),(0,[z1,z2,z444,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z291,z6])],[(0,[z153,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z445,z9,z6]),(0,[z1,z46,z2,z83,z3,z4,z9]),(0,[z1,z446,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z104,z9,z6])],[(0,[z1,z2,z3,z447,z4,z9,z6]),(0,[z448,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z31,z4,z9,z12]),(0,[z70,z1,z2,z3,z32,z9,z6]),(0,[z1,z449,z2,z3,z4,z9,z6])],[(0,[z153,z1,z2,z3,z4,z17,z6]),(1,[z1,z2,z3,z189,z9,z6]),(0,[z27,z1,z2,z3,z4,z9,z450]),(0,[z195,z1,z2,z3,z208,z9,z6]),(1,[z216,z2,z3,z4,z9,z6]),(0,[z1,z25,z2,z3,z31,z9,z6]),(0,[z1,z29,z2,z4,z9,z42,z6])],[(0,[z1,z2,z3,z4,z9,z6,z451]),(0,[z1,z38,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z452,z6])],[(0,[z1,z2,z3,z453,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z222]),(0,[z1,z2,z3,z4,z9,z454,z6]),(0,[z455,z1,z2,z3,z4,z9,z6]),(0,[z23,z456,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z100,z6]),(0,[z1,z2,z3,z4,z9,z452,z19])],[(0,[z125,z1,z2,z3,z4,z9,z6]),(0,[z0,z1,z41,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z457,z9,z6]),(0,[z1,z2,z3,z4,z9,z458,z6]),(0,[z108,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z17,z186,z6]),(0,[z1,z2,z3,z4,z157,z156,z6]),(0,[z1,z46,z2,z3,z4,z17,z6]),(0,[z1,z459,z2,z3,z4,z9,z6]),(0,[z1,z460,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z4,z157,z9,z6]),(0,[z1,z2,z3,z133,z4,z14,z6]),(0,[z1,z461,z2,z3,z4,z9,z6])],[(0,[z1,z24,z2,z3,z4,z9,z462]),(0,[z1,z2,z3,z4,z9,z127,z6]),(0,[z1,z463,z2,z3,z4,z9,z6]),(0,[z1,z123,z2,z3,z4,z14,z6]),(0,[z1,z2,z464,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z176]),(0,[z465,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z19,z63])]],
   [[(0,[z1,z24,z2,z3,z4,z14,z6]),(0,[z107,z1,z2,z3,z36,z9,z6]),(0,[z1,z2,z3,z4,z466,z9,z6]),(0,[z1,z2,z3,z4,z9,z467,z6]),(0,[z1,z2,z3,z4,z468,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z135])],[(0,[z28,z1,z2,z3,z4,z9,z186]),(0,[z1,z2,z3,z4,z157,z14,z6]),(1,[z1,z2,z3,z4,z469,z9])],[(0,[z2,z3,z36,z4,z142,z9,z6]),(0,[z1,z2,z3,z4,z470,z9,z6]),(0,[z1,z2,z3,z4,z9,z12,z43]),(0,[z216,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z238,z4,z9,z6]),(0,[z1,z2,z3,z4,z312,z14,z6]),(0,[z68,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z471,z9,z6])],[(0,[z1,z472,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z32,z202,z9,z6]),(0,[z1,z2,z3,z4,z163,z9,z6]),(0,[z1,z2,z3,z4,z394,z9,z12])],[(0,[z0,z1,z2,z3,z4,z9,z6]),(0,[z1,z473,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z157,z55,z6]),(0,[z1,z2,z3,z4,z9,z6,z474]),(0,[z1,z2,z3,z4,z202,z9,z19]),(0,[z1,z2,z3,z4,z8,z14,z6]),(0,[z1,z2,z3,z4,z9,z231,z6])],[(0,[z1,z2,z3,z475,z4,z9,z6]),(1,[z1,z2,z3,z4,z467,z6]),(0,[z195,z1,z2,z3,z4,z9,z240]),(0,[z1,z2,z3,z11,z4,z9,z6]),(0,[z1,z21,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z476,z6]),(0,[z1,z2,z3,z4,z9,z477,z6]),(0,[z1,z2,z83,z3,z4,z9,z19])],[(0,[z1,z2,z3,z4,z9,z478,z6]),(0,[z1,z2,z3,z4,z9,z450,z6]),(0,[z1,z2,z3,z4,z9,z6,z181]),(0,[z1,z2,z479,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z480,z9,z6])],[(0,[z481,z1,z2,z3,z4,z9,z6]),(0,[z1,z482,z2,z3,z4,z9,z6]),(0,[z195,z1,z2,z3,z4,z483,z6]),(0,[z277,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z484,z9,z6]),(0,[z1,z2,z83,z3,z4,z17,z6])]],
   [[(0,[z1,z2,z485,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z486,z9,z6]),(0,[z1,z2,z3,z4,z166,z9,z6]),(0,[z1,z2,z3,z487,z4,z9,z6]),(0,[z1,z488,z2,z3,z4,z9,z6])],[(0,[z489,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z208,z4,z9,z6]),(0,[z490,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z11,z4,z8,z9,z6]),(0,[z1,z2,z3,z4,z491,z9,z6]),(0,[z1,z2,z3,z4,z9,z19,z426]),(0,[z1,z2,z3,z4,z9,z492,z6])],[(0,[z0,z1,z54,z3,z4,z9,z6]),(0,[z1,z58,z2,z3,z4,z9,z6]),(0,[z1,z2,z109,z3,z4,z9,z6]),(0,[z45,z1,z2,z3,z4,z9,z6]),(0,[z493,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z3,z4,z9,z12]),(0,[z1,z494,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z495,z6]),(0,[z1,z2,z3,z496,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z462,z6]),(1,[z1,z2,z3,z347,z9,z6]),(1,[z1,z2,z120,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z497,z6]),(0,[z1,z2,z3,z32,z4,z9,z322])],[(0,[z1,z25,z2,z3,z4,z9,z12]),(0,[z1,z2,z498,z3,z4,z9,z6]),(0,[z1,z2,z3,z32,z4,z9,z19]),(0,[z1,z29,z2,z3,z4,z9,z12])],[(0,[z1,z2,z3,z4,z9,z6,z499]),(0,[z1,z2,z3,z500,z4,z9,z6]),(0,[z1,z141,z2,z3,z4,z492,z6]),(0,[z1,z2,z3,z4,z96,z9,z12])],[(0,[z153,z1,z24,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z501,z9,z6]),(0,[z1,z2,z3,z4,z502,z9,z6]),(0,[z1,z2,z7,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z4,z17,z6]),(1,[z1,z2,z3,z4,z492,z6])],[(1,[z1,z2,z373,z3,z4,z9]),(0,[z1,z2,z7,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z503,z6]),(0,[z504,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z18,z4,z14,z6]),(0,[z1,z2,z3,z4,z505,z9,z6])]],
   [[(0,[z0,z2,z3,z77,z4,z9,z6]),(0,[z27,z2,z3,z4,z142,z9,z6]),(0,[z1,z506,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z104,z9,z135]),(0,[z1,z2,z3,z4,z9,z42,z81]),(0,[z1,z2,z3,z4,z9,z268,z6]),(0,[z1,z2,z3,z4,z9,z507,z6]),(0,[z508,z1,z2,z3,z4,z9,z6])],[(0,[z27,z1,z509,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z9,z450]),(0,[z1,z2,z3,z4,z9,z240,z6]),(0,[z1,z510,z2,z3,z4,z9,z6]),(0,[z1,z2,z30,z3,z4,z14,z6]),(0,[z45,z1,z2,z3,z4,z9,z173]),(0,[z70,z1,z2,z3,z4,z491,z6]),(0,[z1,z511,z2,z3,z4,z9,z6]),(0,[z512,z1,z2,z3,z4,z9,z6]),(0,[z1,z513,z2,z3,z4,z14,z6]),(0,[z1,z514,z2,z3,z4,z9,z6])],[(0,[z1,z2,z515,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z516]),(0,[z27,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z517,z9,z6]),(0,[z195,z1,z60,z3,z4,z9,z6]),(0,[z1,z375,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z518,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z12,z12])],[(0,[z1,z2,z3,z4,z9,z519,z6]),(0,[z1,z2,z3,z4,z9,z6,z158]),(0,[z1,z2,z3,z4,z9,z520,z6]),(0,[z1,z29,z2,z3,z4,z9,z42]),(0,[z245,z1,z2,z3,z4,z9,z12])],[(0,[z1,z392,z2,z3,z4,z9,z55]),(0,[z1,z2,z3,z4,z14,z186,z6]),(0,[z1,z2,z3,z4,z521,z9,z6])],[(0,[z114,z1,z2,z3,z4,z172,z6]),(0,[z1,z3,z4,z9,z81,z6,z135]),(0,[z1,z61,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z522,z6])],[(0,[z523,z1,z2,z3,z4,z9,z6]),(0,[z1,z524,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z525,z9,z6]),(0,[z1,z175,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z9,z19]),(0,[z1,z2,z3,z4,z9,z526,z6])],[(0,[z1,z2,z3,z527,z4,z9,z6]),(0,[z1,z2,z3,z4,z312,z82,z6]),(0,[z1,z2,z3,z4,z528,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z40]),(0,[z1,z2,z3,z4,z9,z12,z529])]],
   [[(0,[z530,z1,z2,z3,z4,z9,z6]),(0,[z49,z107,z2,z3,z4,z9,z6]),(0,[z531,z1,z2,z3,z4,z9,z6]),(0,[z70,z1,z429,z3,z4,z9,z6]),(0,[z532,z1,z2,z3,z4,z9,z6]),(0,[z1,z74,z2,z3,z9,z14,z6]),(0,[z1,z2,z533,z3,z4,z9,z6])],[(0,[z1,z456,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z42,z6]),(0,[z1,z2,z3,z4,z17,z6,z103]),(0,[z1,z2,z3,z4,z9,z12,z42]),(0,[z374,z1,z2,z3,z4,z9,z19])],[(0,[z1,z534,z2,z3,z4,z9,z6]),(0,[z1,z58,z2,z3,z77,z4,z9]),(0,[z49,z1,z2,z3,z4,z9,z12]),(0,[z10,z1,z535,z3,z4,z9,z6]),(0,[z1,z2,z536,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z81,z103]),(0,[z537,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z538,z9,z6]),(0,[z1,z76,z2,z3,z4,z14,z6])],[(0,[z1,z2,z3,z4,z539,z9,z6]),(0,[z1,z2,z3,z4,z172,z9,z12]),(0,[z1,z2,z3,z241,z4,z9,z6]),(0,[z1,z2,z3,z4,z469,z9,z6]),(0,[z1,z2,z3,z133,z4,z9,z6]),(1,[z1,z2,z3,z35,z9,z19])],[(0,[z1,z2,z3,z4,z540,z9,z6]),(1,[z1,z2,z3,z4,z541,z6]),(0,[z1,z535,z2,z3,z4,z9,z6]),(0,[z1,z123,z2,z3,z4,z9,z6]),(0,[z542,z1,z2,z3,z4,z9,z6]),(0,[z543,z1,z2,z3,z4,z9,z6]),(0,[z465,z1,z2,z3,z4,z9,z6]),(0,[z1,z37,z2,z3,z4,z9,z19])],[(0,[z153,z2,z3,z4,z9,z186,z6]),(1,[z1,z2,z3,z380,z9,z6]),(0,[z1,z2,z544,z3,z4,z9,z6]),(0,[z70,z1,z2,z3,z4,z9,z336]),(0,[z1,z2,z545,z3,z4,z9,z6]),(0,[z1,z29,z2,z3,z4,z104,z9]),(0,[z1,z2,z546,z3,z4,z9,z6]),(1,[z1,z2,z3,z35,z17,z6])],[(0,[z153,z107,z2,z3,z4,z9,z6]),(0,[z1,z547,z2,z3,z4,z9,z6]),(0,[z548,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z549]),(0,[z1,z2,z3,z4,z9,z337,z6]),(1,[z1,z2,z3,z4,z9,z98]),(0,[z68,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z153,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z550,z6]),(0,[z108,z1,z2,z3,z423,z9,z6]),(0,[z1,z2,z11,z4,z9,z82,z6]),(0,[z1,z2,z3,z4,z9,z156,z6]),(0,[z1,z61,z2,z3,z4,z157,z6]),(0,[z1,z2,z3,z4,z17,z6,z368])],[(0,[z1,z2,z3,z551,z4,z9,z6]),(0,[z1,z2,z13,z77,z4,z9,z6]),(0,[z1,z2,z3,z552,z4,z9,z6]),(0,[z1,z2,z553,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z131,z6]),(0,[z1,z554,z2,z3,z4,z9,z6]),(0,[z1,z164,z2,z3,z4,z9,z6]),(0,[z555,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z126,z3,z4,z9,z19]),(1,[z1,z2,z3,z4,z9,z336]),(0,[z395,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z287,z3,z4,z9,z12])],[(0,[z108,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z6,z556]),(0,[z23,z1,z2,z3,z202,z9,z6]),(0,[z1,z46,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z557,z6]),(0,[z70,z1,z2,z3,z4,z14,z6])],[(0,[z1,z2,z126,z3,z4,z17,z6]),(0,[z107,z1,z2,z3,z4,z14,z6]),(0,[z114,z1,z2,z3,z4,z55,z6]),(1,[z1,z2,z3,z4,z337,z6]),(0,[z1,z2,z3,z4,z9,z352,z6]),(0,[z1,z558,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z103,z19]),(0,[z1,z2,z3,z9,z14,z6,z19]),(0,[z1,z2,z3,z4,z9,z559,z6])],[(0,[z1,z2,z3,z36,z8,z9,z6]),(0,[z1,z141,z2,z3,z9,z14,z6]),(0,[z1,z2,z3,z35,z4,z9,z40]),(1,[z1,z141,z2,z3,z9,z12])],[(0,[z1,z126,z3,z4,z202,z9,z6]),(0,[z28,z1,z2,z3,z4,z14,z6]),(0,[z45,z1,z2,z236,z4,z9,z6]),(0,[z1,z325,z2,z3,z4,z9,z156])],[(1,[z1,z2,z3,z4,z9,z462]),(1,[z1,z509,z3,z4,z9,z6]),(0,[z1,z2,z3,z36,z9,z14,z6]),(0,[z1,z2,z3,z4,z9,z6,z560]),(0,[z1,z141,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z17,z9,z14,z6]),(1,[z1,z2,z3,z9,z14,z19])]],
   [[(0,[z1,z126,z3,z11,z4,z9,z6]),(0,[z1,z2,z561,z3,z4,z9,z6]),(0,[z1,z2,z562,z3,z4,z9,z6]),(0,[z1,z2,z3,z563,z4,z9,z6]),(0,[z1,z2,z3,z4,z142,z9,z6]),(0,[z1,z2,z3,z32,z142,z9,z6]),(0,[z1,z564,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z565,z6]),(1,[z1,z2,z3,z4,z14,z6])],[(0,[z566,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z142,z9,z19]),(1,[z1,z2,z3,z4,z567,z9]),(0,[z1,z2,z3,z4,z9,z6,z122]),(0,[z1,z60,z2,z30,z4,z9,z6]),(0,[z45,z1,z2,z3,z241,z9,z6]),(0,[z1,z2,z13,z3,z8,z9,z6])],[(0,[z1,z2,z3,z4,z9,z6,z568]),(0,[z1,z2,z3,z4,z569,z9,z6]),(0,[z1,z2,z3,z4,z9,z570,z6]),(0,[z1,z2,z3,z4,z16,z9,z6]),(0,[z1,z571,z2,z3,z4,z9,z6]),(0,[z1,z29,z2,z3,z4,z17,z6])],[(0,[z23,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z31,z8,z9,z6]),(0,[z1,z2,z13,z3,z9,z14,z6]),(1,[z1,z2,z83,z4,z9,z103])],[(0,[z195,z1,z2,z11,z4,z9,z6]),(0,[z195,z1,z2,z3,z4,z17,z6]),(0,[z23,z1,z2,z3,z4,z9,z19]),(0,[z572,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z573,z9,z6]),(0,[z1,z2,z83,z3,z4,z9,z12]),(0,[z1,z2,z3,z18,z4,z9,z6]),(0,[z1,z2,z20,z3,z4,z9,z6])],[(0,[z574,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z31,z9,z14,z6]),(0,[z1,z123,z2,z3,z4,z312,z6]),(0,[z1,z2,z3,z4,z575,z9,z6]),(0,[z572,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z19,z75]),(0,[z1,z2,z3,z4,z9,z6,z19])],[(0,[z1,z2,z30,z3,z4,z9,z6]),(0,[z195,z1,z3,z11,z4,z9,z6]),(0,[z23,z1,z3,z4,z202,z9,z6]),(0,[z1,z2,z3,z4,z9,z576,z6]),(1,[z1,z2,z3,z4,z274,z6]),(0,[z1,z513,z2,z3,z4,z9,z6])],[(0,[z2,z126,z3,z4,z9,z186,z6]),(0,[z1,z2,z577,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z157,z312,z6]),(0,[z578,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z14,z6,z103]),(0,[z1,z2,z579,z3,z4,z9,z6]),(0,[z1,z2,z48,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z580,z4,z9,z6]),(0,[z1,z2,z3,z4,z423,z9,z6]),(0,[z1,z2,z3,z4,z9,z42,z135])],[(0,[z1,z2,z3,z4,z567,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z581]),(0,[z1,z582,z2,z3,z4,z9,z6])],[(1,[z1,z2,z3,z4,z9,z226]),(1,[z1,z535,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z202,z9,z6]),(0,[z1,z61,z2,z3,z4,z9,z6]),(0,[z1,z583,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z584,z9,z6]),(0,[z1,z46,z2,z3,z4,z9,z186]),(0,[z1,z2,z3,z4,z104,z9,z81]),(0,[z1,z2,z3,z32,z4,z9,z12]),(0,[z1,z61,z2,z3,z4,z9,z19]),(0,[z1,z2,z83,z3,z4,z9,z42]),(0,[z1,z2,z3,z585,z4,z9,z6]),(0,[z1,z2,z3,z4,z586,z9,z6]),(0,[z1,z2,z3,z4,z587,z9,z6]),(0,[z1,z2,z3,z4,z4,z9,z12])],[(0,[z1,z2,z588,z3,z4,z9,z6]),(0,[z589,z1,z2,z3,z4,z9,z6]),(0,[z45,z277,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z587,z9,z19]),(0,[z1,z2,z3,z4,z9,z344,z12])],[(1,[z1,z2,z3,z4,z437,z6]),(1,[z1,z2,z3,z4,z9,z190]),(0,[z1,z2,z3,z4,z9,z590,z6]),(0,[z1,z2,z3,z4,z9,z591,z19])],[(0,[z1,z2,z3,z592,z4,z9,z6]),(0,[z1,z2,z3,z77,z4,z14,z6]),(0,[z1,z2,z3,z36,z4,z9,z190]),(0,[z1,z2,z3,z593,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z401,z6]),(0,[z68,z1,z2,z3,z4,z9,z135]),(0,[z1,z2,z3,z4,z17,z6,z63]),(0,[z1,z2,z3,z4,z104,z96,z9])],[(1,[z1,z25,z3,z31,z9,z6]),(0,[z1,z2,z3,z4,z9,z81,z63]),(1,[z1,z2,z13,z3,z14,z6]),(0,[z1,z2,z3,z365,z4,z9,z6]),(0,[z594,z1,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z157,z172,z6]),(0,[z1,z29,z46,z2,z3,z4,z9]),(0,[z1,z2,z3,z595,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z82,z6])],[(0,[z1,z2,z3,z238,z4,z9,z6]),(0,[z1,z596,z2,z3,z4,z9,z6]),(0,[z1,z597,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z598,z4,z9,z6]),(1,[z1,z2,z3,z4,z17,z12]),(0,[z1,z2,z3,z4,z17,z12,z6])],[(0,[z1,z2,z3,z4,z9,z599,z6]),(0,[z70,z1,z2,z3,z4,z88,z6]),(0,[z1,z2,z3,z35,z4,z9,z162])],[(0,[z1,z2,z3,z4,z600,z9,z6]),(0,[z108,z1,z2,z120,z4,z9,z6]),(0,[z1,z601,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z4,z9,z19]),(0,[z1,z2,z602,z3,z4,z9,z6])],[(0,[z603,z1,z2,z3,z4,z9,z6]),(0,[z604,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z31,z4,z9,z191]),(0,[z1,z2,z3,z605,z4,z9,z6]),(0,[z1,z2,z3,z4,z606,z9,z6]),(0,[z1,z2,z3,z4,z9,z607,z6])],[(0,[z1,z123,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z541,z9,z6]),(0,[z23,z1,z25,z3,z4,z9,z6]),(0,[z23,z1,z2,z3,z4,z9,z205]),(0,[z1,z2,z83,z3,z4,z104,z9]),(0,[z1,z2,z3,z4,z17,z9,z12]),(0,[z1,z2,z3,z4,z104,z9,z19])],[(0,[z1,z2,z3,z4,z9,z255,z6]),(0,[z114,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z13,z30,z4,z9,z6]),(1,[z1,z2,z310,z4,z9,z6]),(0,[z1,z325,z2,z3,z4,z9,z6]),(0,[z70,z129,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z608,z6]),(0,[z1,z105,z2,z3,z4,z9,z6])],[(1,[z1,z41,z3,z4,z9,z6]),(0,[z1,z2,z609,z3,z4,z9,z6]),(0,[z114,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z6,z610]),(0,[z1,z2,z168,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z17,z424,z6])]],
   [[(0,[z27,z1,z2,z611,z4,z9,z6]),(0,[z612,z1,z2,z3,z4,z9,z6]),(0,[z28,z2,z3,z4,z9,z6,z43]),(1,[z1,z2,z3,z97,z9,z6]),(0,[z70,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z96,z9,z103]),(0,[z1,z2,z3,z4,z39,z9,z6])],[(1,[z153,z24,z3,z4,z9,z6]),(0,[z1,z25,z2,z3,z4,z14,z6]),(0,[z613,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z614,z3,z4,z9,z6])],[(0,[z125,z1,z2,z3,z4,z9,z19]),(1,[z218,z2,z3,z4,z9,z6]),(0,[z615,z1,z2,z3,z4,z9,z6]),(0,[z616,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z96,z14,z6])],[(0,[z1,z126,z3,z4,z9,z156,z6]),(0,[z49,z1,z2,z77,z4,z9,z6]),(0,[z1,z2,z611,z3,z4,z9,z6]),(0,[z28,z1,z2,z3,z4,z9,z6]),(0,[z617,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z3,z9,z110,z6]),(0,[z1,z37,z2,z3,z4,z9,z12]),(1,[z1,z2,z3,z4,z96,z63])],[(0,[z1,z2,z3,z32,z36,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z43]),(0,[z1,z618,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z17,z9,z6]),(0,[z1,z461,z2,z3,z4,z17,z6])],[(0,[z0,z1,z2,z3,z4,z9,z127]),(0,[z1,z619,z2,z3,z4,z9,z6]),(0,[z1,z129,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z12,z103]),(0,[z1,z2,z3,z4,z9,z19,z19]),(0,[z1,z271,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z620])],[(0,[z49,z2,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z621,z6]),(0,[z1,z2,z3,z622,z4,z9,z6]),(0,[z1,z136,z2,z3,z4,z9,z6]),(0,[z1,z30,z3,z11,z4,z9,z6]),(0,[z1,z2,z3,z4,z469,z157,z9]),(0,[z1,z2,z3,z4,z14,z214,z6]),(0,[z386,z1,z2,z3,z4,z9,z12])],[(0,[z1,z1,z2,z3,z4,z9,z6]),(0,[z623,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z142,z8,z9,z6]),(0,[z1,z2,z624,z3,z4,z9,z6]),(0,[z1,z2,z13,z3,z32,z9,z6]),(0,[z1,z2,z3,z18,z4,z65,z6]),(0,[z1,z2,z3,z4,z9,z625,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z9,z19]),(0,[z1,z2,z626,z3,z4,z9,z6]),(0,[z1,z627,z2,z3,z4,z9,z6])],[(0,[z1,z2,z126,z3,z4,z9,z12]),(0,[z628,z1,z2,z3,z4,z9,z6]),(0,[z1,z629,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z11,z4,z9,z19]),(0,[z1,z2,z3,z4,z202,z17,z6]),(0,[z1,z2,z4,z9,z42,z6,z103]),(0,[z630,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z19,z581])],[(0,[z2,z3,z4,z9,z186,z6,z43]),(0,[z631,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z632,z4,z9,z6]),(0,[z1,z37,z2,z3,z4,z9,z42]),(0,[z1,z2,z3,z4,z480,z9,z19])],[(0,[z1,z633,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z347,z9,z6]),(0,[z1,z2,z3,z11,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z634,z6])],[(0,[z1,z2,z635,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z135,z19]),(0,[z1,z2,z3,z4,z100,z9,z6]),(0,[z1,z2,z3,z4,z14,z6,z63])],[(0,[z153,z49,z2,z3,z4,z9,z6]),(0,[z49,z2,z3,z4,z142,z9,z6]),(0,[z420,z1,z2,z3,z4,z9,z6]),(0,[z108,z1,z2,z3,z380,z9,z6]),(0,[z1,z2,z3,z4,z9,z186,z103]),(0,[z1,z636,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z157,z9,z110,z6]),(0,[z637,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z638,z6])],[(0,[z1,z2,z3,z639,z4,z9,z6]),(0,[z1,z2,z3,z115,z11,z4,z9]),(0,[z1,z2,z3,z640,z4,z9,z6]),(0,[z45,z1,z2,z3,z4,z9,z19]),(0,[z68,z1,z29,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z174,z9,z6]),(0,[z1,z2,z3,z4,z641,z9,z6])],[(0,[z1,z2,z77,z4,z9,z82,z6]),(0,[z1,z642,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z379,z156]),(0,[z1,z2,z3,z4,z9,z643,z6]),(0,[z68,z1,z46,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z6,z135]),(0,[z68,z1,z37,z2,z3,z4,z9]),(0,[z270,z1,z2,z3,z4,z14,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z298,z6]),(0,[z1,z2,z3,z644,z4,z9,z6]),(0,[z1,z2,z168,z30,z4,z9,z6]),(0,[z45,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z6,z33]),(0,[z1,z2,z3,z645,z4,z9,z6])],[(0,[z195,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z32,z4,z17,z6]),(1,[z1,z2,z3,z365,z9,z6])],[(0,[z1,z646,z2,z3,z4,z9,z6]),(0,[z1,z3,z4,z312,z9,z156,z6]),(1,[z1,z61,z2,z4,z82,z6]),(1,[z1,z2,z3,z14,z6,z19]),(0,[z1,z2,z3,z96,z9,z291,z6])],[(0,[z1,z2,z647,z3,z4,z9,z6]),(0,[z153,z2,z3,z4,z142,z9,z6]),(0,[z1,z2,z3,z77,z4,z9,z6]),(1,[z1,z2,z109,z4,z9,z6]),(0,[z1,z648,z2,z3,z4,z9,z6]),(0,[z1,z2,z649,z3,z4,z9,z6]),(0,[z10,z1,z2,z3,z4,z14,z6]),(1,[z375,z2,z3,z4,z9,z6])],[(0,[z1,z2,z7,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z567,z9,z55]),(0,[z1,z2,z650,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z104,z9,z43]),(0,[z1,z2,z3,z4,z9,z651,z6]),(0,[z1,z2,z168,z3,z4,z82,z6]),(0,[z1,z2,z3,z4,z12,z14,z6]),(0,[z1,z2,z3,z4,z9,z6,z591]),(0,[z1,z2,z3,z652,z4,z9,z6]),(0,[z1,z37,z2,z3,z4,z104,z9])],[(0,[z1,z2,z3,z653,z4,z9,z6]),(0,[z654,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z394,z9,z6]),(0,[z1,z2,z3,z4,z9,z529,z6])],[(0,[z655,z1,z2,z3,z4,z9,z6]),(1,[z1,z2,z611,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z256,z6]),(0,[z1,z2,z3,z656,z4,z9,z6]),(0,[z1,z2,z657,z3,z4,z9,z6]),(0,[z1,z658,z2,z3,z4,z9,z6]),(0,[z659,z1,z2,z3,z4,z9,z6]),(0,[z508,z1,z2,z3,z4,z17,z6])],[(0,[z125,z1,z24,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z660]),(0,[z1,z2,z3,z35,z142,z9,z6]),(0,[z1,z2,z3,z4,z96,z82,z6]),(0,[z1,z661,z2,z3,z4,z9,z6]),(0,[z1,z662,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z663,z3,z4,z9,z6]),(0,[z108,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z664,z6]),(0,[z1,z2,z3,z4,z665,z9,z6]),(0,[z1,z46,z2,z3,z4,z14,z6])],[(1,[z1,z2,z3,z4,z234,z6]),(0,[z68,z1,z2,z3,z4,z9,z81]),(1,[z1,z2,z3,z4,z491,z6]),(0,[z1,z2,z3,z4,z9,z239,z6]),(0,[z1,z2,z3,z4,z9,z666,z6])],[(0,[z1,z2,z3,z4,z9,z667,z6]),(0,[z28,z1,z2,z3,z4,z9,z135]),(1,[z456,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z205,z6]),(1,[z1,z141,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z9,z391,z6]),(0,[z1,z37,z2,z3,z4,z104,z6])],[(0,[z1,z2,z3,z4,z399,z9,z6]),(0,[z1,z60,z2,z3,z4,z14,z6]),(1,[z1,z2,z3,z4,z9,z176]),(0,[z1,z2,z3,z4,z17,z17,z6])],[(0,[z1,z2,z3,z4,z668,z9,z6]),(0,[z1,z2,z509,z3,z4,z9,z6]),(0,[z669,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z43,z103]),(0,[z1,z2,z3,z4,z9,z670,z6]),(0,[z10,z1,z29,z2,z3,z4,z9]),(0,[z68,z1,z2,z3,z4,z96,z9])],[(0,[z671,z1,z2,z3,z4,z9,z6]),(0,[z23,z1,z2,z3,z4,z228,z6]),(0,[z1,z2,z3,z4,z9,z42,z19]),(0,[z1,z74,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z96,z9,z63]),(0,[z1,z2,z3,z4,z104,z6,z63])],[(0,[z1,z672,z2,z3,z4,z9,z6]),(0,[z1,z25,z2,z3,z4,z9,z6]),(0,[z1,z3,z31,z4,z202,z9,z6]),(0,[z1,z2,z3,z4,z9,z435,z12])],[(0,[z673,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z83,z3,z4,z9,z103]),(0,[z1,z2,z3,z4,z9,z405,z6]),(0,[z1,z2,z3,z4,z96,z9,z6])]],
   [[(0,[z1,z24,z2,z3,z4,z9,z6]),(0,[z1,z2,z674,z3,z4,z9,z6]),(0,[z1,z2,z3,z36,z4,z541,z6]),(0,[z675,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z173,z6]),(0,[z1,z123,z2,z3,z4,z9,z19]),(1,[z1,z429,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z65,z6])],[(0,[z1,z24,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z157,z9,z6]),(0,[z1,z2,z3,z4,z676,z9,z6]),(0,[z1,z37,z2,z3,z4,z17,z6])],[(0,[z125,z1,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z677,z9,z6]),(1,[z1,z2,z3,z4,z9,z181]),(0,[z1,z2,z3,z4,z9,z678,z6]),(0,[z1,z2,z3,z4,z312,z9,z6]),(0,[z1,z123,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z157,z9,z19]),(0,[z1,z2,z679,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z4,z9,z12])],[(0,[z1,z24,z3,z4,z202,z9,z6]),(0,[z1,z680,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z681,z6]),(0,[z10,z1,z79,z3,z4,z9,z6]),(0,[z195,z1,z2,z3,z4,z467,z6]),(1,[z1,z2,z3,z202,z14,z6]),(0,[z1,z2,z3,z4,z312,z9,z19]),(0,[z68,z1,z2,z3,z4,z9,z19]),(0,[z682,z1,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z156,z19]),(0,[z1,z2,z683,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z8,z9,z6]),(0,[z1,z2,z3,z4,z104,z9,z12]),(0,[z684,z1,z2,z3,z4,z9,z6])],[(0,[z2,z126,z3,z4,z142,z9,z6]),(0,[z685,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z172,z82,z6]),(0,[z1,z2,z3,z4,z9,z12,z186]),(1,[z1,z60,z30,z4,z9,z6]),(0,[z1,z2,z3,z32,z31,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z128]),(0,[z1,z2,z3,z4,z14,z6,z135]),(0,[z68,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z8,z9,z19]),(0,[z1,z2,z3,z4,z686,z9,z6]),(0,[z1,z554,z2,z3,z4,z9,z19])],[(0,[z24,z2,z126,z3,z4,z9,z6]),(1,[z1,z2,z3,z4,z483,z6]),(0,[z1,z2,z3,z4,z687,z9,z6]),(0,[z1,z2,z688,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z14,z6]),(0,[z1,z141,z2,z3,z9,z12,z6])],[(0,[z10,z1,z2,z3,z4,z9,z81]),(0,[z1,z2,z3,z4,z9,z379,z6]),(0,[z1,z2,z3,z4,z9,z689,z6]),(1,[z1,z29,z2,z4,z9,z42]),(0,[z1,z2,z3,z4,z9,z14,z19])]],
   [[(0,[z1,z2,z3,z690,z4,z9,z6]),(0,[z70,z1,z2,z3,z4,z9,z268]),(0,[z1,z2,z3,z4,z17,z42,z6]),(0,[z1,z2,z3,z4,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z559,z19])],[(0,[z125,z1,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z691,z6]),(0,[z1,z2,z3,z692,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z55,z6]),(0,[z1,z2,z3,z4,z693,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z694]),(0,[z1,z695,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z696,z9,z6])],[(0,[z153,z114,z2,z3,z4,z9,z6]),(0,[z697,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z269,z9,z6]),(1,[z1,z2,z3,z4,z9,z354]),(0,[z1,z2,z3,z4,z698,z9,z6]),(0,[z1,z2,z3,z4,z9,z186,z63]),(0,[z1,z2,z3,z4,z483,z9,z6]),(0,[z1,z2,z3,z4,z9,z6,z331]),(0,[z1,z61,z2,z168,z4,z9,z6]),(1,[z1,z2,z3,z4,z244,z6]),(0,[z1,z2,z3,z9,z12,z6,z19])],[(0,[z699,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z36,z4,z9,z354]),(0,[z1,z2,z3,z4,z9,z6,z700]),(0,[z1,z2,z701,z3,z4,z9,z6])],[(0,[z270,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z36,z4,z14,z6]),(0,[z1,z702,z2,z3,z4,z9,z6]),(0,[z23,z1,z2,z343,z4,z9,z6]),(0,[z71,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z274,z6]),(1,[z1,z2,z3,z4,z14,z19])],[(0,[z108,z114,z2,z3,z4,z9,z6]),(0,[z45,z1,z3,z4,z9,z156,z6])],[(0,[z1,z2,z3,z4,z703,z9,z6]),(0,[z1,z2,z3,z4,z142,z17,z6]),(0,[z1,z2,z3,z4,z202,z9,z12]),(0,[z1,z278,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z437,z9,z6]),(0,[z0,z1,z2,z3,z4,z9,z12]),(0,[z1,z704,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z156,z6]),(0,[z1,z37,z46,z2,z3,z4,z9]),(0,[z1,z2,z3,z705,z4,z9,z6]),(0,[z1,z2,z706,z3,z4,z9,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z707,z9,z6]),(0,[z161,z2,z3,z142,z9,z6]),(0,[z1,z2,z3,z4,z9,z708]),(0,[z1,z46,z3,z4,z9,z135]),(0,[z1,z2,z168,z3,z110,z6])],[(0,[z1,z2,z3,z4,z709,z6]),(0,[z49,z1,z2,z3,z14,z19]),(0,[z1,z535,z3,z4,z9,z43]),(0,[z1,z618,z30,z4,z9,z6]),(0,[z1,z29,z2,z4,z14,z42]),(0,[z1,z2,z710,z4,z14,z6])],[(0,[z1,z2,z3,z4,z14,z255]),(0,[z1,z2,z3,z4,z399,z95]),(0,[z1,z2,z3,z4,z14,z256]),(0,[z1,z2,z3,z35,z17,z40]),(0,[z1,z711,z3,z4,z9,z12])],[(0,[z1,z2,z3,z347,z9,z127]),(0,[z1,z2,z3,z712,z9,z6]),(0,[z1,z2,z713,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z173]),(0,[z1,z167,z3,z32,z9,z6]),(0,[z374,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z291,z6,z63])],[(0,[z1,z2,z3,z4,z714,z6]),(0,[z107,z509,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z715]),(0,[z70,z1,z2,z8,z9,z12]),(0,[z716,z2,z3,z4,z9,z6]),(0,[z1,z2,z717,z4,z9,z6]),(0,[z1,z2,z718,z4,z9,z19])],[(0,[z1,z2,z3,z4,z719,z6]),(0,[z1,z702,z2,z4,z82,z6]),(0,[z23,z1,z3,z202,z14,z6])],[(0,[z578,z2,z77,z4,z9,z6]),(0,[z1,z509,z3,z4,z9,z12]),(0,[z1,z2,z3,z31,z720,z6]),(0,[z1,z2,z3,z96,z291,z63])],[(0,[z28,z2,z3,z4,z9,z209]),(0,[z71,z2,z3,z4,z491,z6]),(0,[z1,z2,z3,z4,z14,z268]),(0,[z1,z2,z3,z4,z721,z6])],[(0,[z1,z722,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z723]),(0,[z1,z2,z120,z4,z17,z6]),(0,[z1,z2,z3,z4,z379,z14])],[(0,[z1,z2,z3,z551,z14,z6]),(0,[z46,z126,z3,z4,z9,z186]),(0,[z1,z2,z3,z4,z724,z6]),(0,[z277,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z188]),(0,[z1,z2,z3,z365,z9,z19]),(0,[z1,z2,z3,z14,z6,z19])],[(0,[z1,z2,z109,z4,z9,z6]),(0,[z1,z2,z3,z142,z390,z6]),(0,[z1,z2,z3,z4,z9,z725]),(0,[z1,z2,z3,z4,z267,z63]),(0,[z1,z2,z3,z4,z726,z6]),(0,[z1,z2,z3,z241,z9,z727]),(0,[z1,z61,z2,z4,z82,z19]),(0,[z1,z2,z3,z157,z291,z6])],[(0,[z153,z304,z3,z4,z9,z6]),(0,[z1,z2,z3,z172,z14,z19]),(0,[z1,z2,z3,z656,z9,z19]),(0,[z375,z2,z3,z4,z9,z19]),(0,[z728,z2,z3,z4,z9,z6]),(0,[z1,z129,z2,z8,z9,z6])],[(0,[z1,z729,z2,z3,z4,z9]),(0,[z1,z3,z4,z312,z730,z6]),(0,[z684,z1,z3,z4,z9,z81]),(0,[z1,z2,z3,z4,z9,z731]),(0,[z1,z2,z3,z4,z96,z522])],[(0,[z1,z2,z3,z4,z9,z732]),(0,[z1,z2,z238,z4,z9,z98]),(0,[z1,z2,z3,z4,z379,z82]),(0,[z1,z2,z3,z9,z291,z103]),(0,[z1,z2,z3,z4,z14,z40]),(0,[z1,z2,z3,z18,z9,z733])],[(0,[z1,z2,z611,z4,z9,z19]),(0,[z1,z85,z3,z4,z9,z181]),(0,[z218,z2,z3,z208,z9,z6]),(0,[z734,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z205]),(0,[z335,z2,z3,z4,z9,z12]),(0,[z71,z429,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z735]),(0,[z1,z2,z3,z592,z14,z6]),(0,[z1,z2,z3,z736,z9,z6]),(0,[z1,z37,z2,z3,z4,z737])]],
   [[(0,[z1,z294,z3,z4,z14,z6]),(0,[z1,z74,z2,z3,z12,z14])],[(0,[z28,z2,z3,z4,z9,z251]),(0,[z1,z2,z3,z4,z738,z6]),(0,[z1,z535,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z82,z239]),(0,[z1,z2,z83,z4,z9,z731]),(0,[z1,z141,z2,z3,z14,z6])],[(0,[z1,z34,z3,z4,z9,z6]),(0,[z1,z739,z3,z4,z9,z6]),(0,[z27,z509,z3,z142,z9,z6]),(0,[z456,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z176])],[(0,[z2,z77,z142,z8,z9,z6]),(0,[z1,z2,z3,z4,z9,z740]),(0,[z1,z276,z2,z3,z14,z6]),(0,[z741,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z487,z14,z6])],[(0,[z1,z2,z3,z4,z9,z742])],[(0,[z70,z1,z2,z3,z12,z14]),(0,[z1,z2,z3,z4,z743,z6])],[(0,[z1,z2,z3,z4,z9,z744]),(0,[z2,z3,z4,z745,z9,z6]),(0,[z1,z2,z3,z746,z9,z6]),(0,[z1,z747,z3,z4,z9,z6]),(0,[z245,z1,z3,z4,z9,z344])],[(0,[z1,z2,z3,z4,z9,z748]),(0,[z1,z2,z3,z347,z9,z749]),(0,[z2,z77,z4,z347,z9,z6]),(0,[z1,z2,z750,z3,z4,z9]),(0,[z1,z2,z3,z4,z541,z19]),(0,[z1,z85,z3,z4,z14,z6]),(0,[z1,z2,z343,z4,z9,z98]),(0,[z1,z2,z167,z3,z14,z6])],[(0,[z1,z2,z4,z751,z9,z6])],[(0,[z153,z752,z3,z4,z9,z6]),(0,[z1,z2,z3,z753,z9,z6]),(0,[z1,z2,z3,z4,z399,z12]),(0,[z1,z2,z3,z470,z14,z6]),(0,[z28,z1,z2,z3,z9,z291]),(0,[z313,z2,z3,z4,z9,z186])],[(0,[z2,z126,z373,z3,z4,z9]),(0,[z1,z58,z2,z3,z4,z14]),(0,[z1,z2,z3,z380,z17,z6]),(0,[z1,z2,z3,z4,z483,z122]),(0,[z1,z2,z3,z605,z14,z6]),(0,[z1,z2,z3,z754,z9,z6]),(0,[z1,z429,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z755]),(0,[z1,z2,z168,z4,z756,z6]),(0,[z1,z105,z2,z4,z9,z559])],[(0,[z1,z2,z3,z4,z9,z757]),(0,[z1,z2,z3,z202,z14,z19]),(0,[z1,z2,z3,z4,z17,z758])],[(0,[z1,z2,z3,z4,z9,z759]),(0,[z136,z2,z3,z4,z483,z6]),(0,[z1,z60,z30,z4,z9,z6]),(0,[z1,z2,z3,z35,z491,z6]),(0,[z1,z338,z2,z4,z82,z6])],[(0,[z216,z2,z3,z4,z9,z12]),(0,[z1,z2,z310,z4,z9,z12]),(0,[z1,z2,z3,z480,z14,z6])],[(0,[z1,z2,z3,z4,z567,z157]),(0,[z1,z2,z3,z4,z9,z760]),(0,[z114,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z483,z19]),(1,[z1,z167,z8,z9,z6]),(0,[z1,z2,z3,z4,z88,z268])],[(0,[z1,z41,z3,z4,z5,z6]),(0,[z1,z60,z761,z4,z9,z6]),(0,[z1,z2,z3,z166,z14,z6]),(0,[z70,z129,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z762,z6]),(0,[z1,z2,z3,z9,z12,z19])]],
   [[(0,[z1,z2,z3,z4,z14,z127]),(0,[z1,z2,z635,z3,z14,z6]),(0,[z1,z2,z343,z4,z14,z6]),(0,[z1,z2,z3,z202,z274,z6]),(0,[z1,z46,z3,z632,z4,z9]),(0,[z1,z2,z3,z4,z14,z763])],[(0,[z68,z1,z3,z4,z9,z764]),(0,[z1,z2,z3,z14,z19,z19])],[(0,[z1,z2,z3,z4,z9,z765]),(0,[z1,z2,z3,z4,z9,z766]),(0,[z1,z2,z3,z4,z244,z19])],[(0,[z1,z2,z3,z4,z767,z6]),(0,[z1,z60,z3,z97,z9,z6]),(0,[z1,z2,z3,z9,z768,z6]),(0,[z1,z2,z48,z3,z14,z6])],[(0,[z1,z2,z3,z4,z17,z462]),(0,[z1,z509,z3,z4,z9,z450]),(0,[z1,z2,z3,z4,z17,z354]),(0,[z1,z2,z3,z4,z9,z769]),(1,[z1,z3,z4,z9,z764]),(0,[z1,z2,z3,z9,z110,z158]),(0,[z1,z2,z3,z4,z9,z231])],[(0,[z0,z2,z77,z4,z437,z6]),(0,[z45,z1,z236,z4,z156,z6]),(0,[z1,z2,z3,z4,z770,z6]),(0,[z1,z2,z83,z4,z9,z144]),(0,[z1,z771,z3,z4,z9,z6]),(0,[z1,z2,z3,z14,z19,z581]),(0,[z1,z2,z772,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z158])],[(0,[z1,z2,z3,z189,z9,z222]),(0,[z216,z2,z3,z4,z228,z6]),(0,[z1,z773,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z774,z6]),(0,[z45,z1,z3,z241,z156,z6]),(0,[z1,z2,z3,z14,z135,z19]),(0,[z1,z2,z3,z4,z17,z775])],[(0,[z1,z2,z776,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z777]),(0,[z1,z2,z3,z4,z9,z778]),(0,[z1,z2,z3,z779,z39,z6]),(0,[z1,z2,z3,z14,z638,z6])],[(0,[z1,z2,z120,z423,z9,z6]),(0,[z1,z535,z83,z3,z4,z9]),(0,[z1,z2,z3,z4,z39,z6]),(0,[z1,z2,z3,z9,z291,z63])],[],[(0,[z1,z2,z3,z4,z9,z780]),(0,[z1,z2,z3,z4,z9,z781]),(0,[z1,z25,z2,z3,z14,z19]),(0,[z1,z167,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z782,z6]),(0,[z1,z2,z3,z17,z14,z6])],[(0,[z1,z2,z3,z4,z783,z6]),(0,[z1,z2,z120,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z784]),(0,[z785,z2,z3,z4,z9,z6]),(0,[z1,z786,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z787]),(0,[z1,z2,z3,z705,z9,z19]),(0,[z1,z2,z168,z365,z157,z6])],[(0,[z0,z41,z77,z4,z9,z6]),(0,[z1,z2,z3,z4,z788,z6]),(0,[z1,z2,z3,z4,z9,z789]),(0,[z1,z2,z614,z3,z14,z6]),(0,[z1,z164,z2,z3,z4,z104])]],
   [[(0,[z1,z24,z3,z202,z14,z6]),(0,[z1,z790,z3,z4,z9,z6]),(0,[z108,z2,z120,z4,z55,z6]),(0,[z1,z2,z3,z4,z9,z791]),(0,[z792,z2,z3,z4,z9,z6]),(0,[z1,z554,z3,z4,z9,z135])],[(0,[z1,z2,z3,z4,z289,z6]),(0,[z793,z2,z3,z4,z9,z6]),(0,[z794,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z31,z401,z14]),(0,[z795,z2,z3,z4,z17,z6]),(0,[z1,z170,z2,z3,z9,z12])],[(0,[z1,z509,z3,z4,z9,z95]),(0,[z1,z2,z3,z208,z796,z6])],[(0,[z1,z79,z3,z4,z9,z19]),(0,[z1,z2,z3,z215,z14,z6]),(0,[z70,z1,z2,z8,z9,z336])],[(0,[z2,z126,z3,z4,z567,z9]),(0,[z1,z797,z2,z3,z4,z9]),(0,[z108,z1,z2,z3,z14,z19]),(0,[z1,z105,z2,z3,z14,z19])],[(0,[z1,z85,z3,z4,z9,z19]),(0,[z1,z2,z3,z31,z337,z6])],[(0,[z1,z2,z3,z4,z9,z798]),(0,[z71,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z196,z9,z12]),(1,[z1,z2,z3,z768,z6]),(0,[z1,z2,z3,z92,z9,z19])],[(0,[z1,z2,z3,z347,z9,z222]),(0,[z1,z2,z3,z4,z399,z450]),(0,[z1,z2,z3,z4,z799,z9]),(0,[z1,z2,z236,z241,z9,z6]),(0,[z1,z2,z3,z4,z9,z800])],[(0,[z1,z2,z3,z4,z9,z801]),(0,[z1,z3,z761,z4,z9,z6]),(0,[z45,z1,z3,z4,z379,z156]),(0,[z1,z2,z3,z4,z491,z12])],[(0,[z195,z1,z11,z4,z14,z6]),(0,[z1,z2,z3,z4,z802,z6]),(0,[z803,z2,z3,z4,z9,z6]),(0,[z1,z2,z804,z4,z9,z6]),(0,[z805,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z14,z42,z19]),(0,[z1,z2,z3,z4,z737,z63])],[(0,[z699,z1,z2,z3,z14,z6]),(0,[z1,z2,z3,z806,z9,z6]),(0,[z1,z46,z3,z4,z9,z764]),(0,[z1,z2,z3,z4,z88,z19])],[(0,[z1,z2,z807,z4,z9,z6]),(0,[z1,z2,z3,z9,z808,z6]),(0,[z612,z1,z2,z8,z9,z6]),(0,[z136,z2,z3,z4,z9,z122]),(0,[z1,z2,z3,z115,z4,z9]),(0,[z1,z2,z310,z4,z17,z6])],[(0,[z1,z41,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z809]),(0,[z1,z2,z3,z4,z483,z240]),(0,[z1,z2,z3,z166,z9,z810])],[(0,[z395,z2,z3,z4,z9,z43]),(0,[z1,z2,z11,z97,z9,z6]),(0,[z1,z2,z3,z97,z17,z6]),(0,[z1,z2,z3,z4,z811,z6]),(0,[z129,z2,z13,z4,z9,z6]),(0,[z1,z2,z13,z32,z9,z19]),(1,[z1,z2,z3,z291,z63])],[(0,[z125,z126,z3,z4,z9,z19]),(0,[z153,z24,z3,z4,z17,z6]),(0,[z153,z2,z3,z4,z9,z462]),(0,[z1,z2,z3,z347,z812,z6]),(0,[z1,z2,z3,z4,z9,z813])],[(0,[z1,z2,z814,z4,z9,z6]),(0,[z0,z2,z373,z77,z4,z9]),(0,[z1,z815,z2,z3,z4,z9]),(0,[z1,z2,z3,z142,z14,z6]),(0,[z1,z2,z3,z380,z9,z12]),(0,[z136,z2,z3,z4,z9,z19]),(0,[z218,z2,z3,z4,z17,z6]),(0,[z1,z3,z11,z97,z9,z6]),(0,[z1,z2,z3,z31,z274,z6]),(0,[z1,z429,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z162]),(0,[z1,z330,z2,z3,z14,z19])]],
   [[(0,[z1,z2,z3,z4,z9,z816]),(0,[z28,z2,z545,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z817]),(0,[z129,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z818,z9,z6])],[(0,[z1,z2,z3,z4,z12,z289]),(0,[z45,z277,z3,z4,z156,z6]),(0,[z1,z2,z4,z157,z756,z6]),(0,[z1,z2,z3,z14,z131,z19])],[(0,[z1,z2,z3,z4,z17,z6]),(0,[z448,z24,z3,z4,z9,z6]),(0,[z108,z2,z3,z380,z55,z6]),(0,[z1,z2,z3,z4,z9,z819]),(0,[z820,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z211,z75])],[(0,[z1,z54,z3,z4,z9,z127]),(0,[z1,z2,z3,z4,z9,z821]),(0,[z1,z111,z3,z31,z9,z6]),(0,[z375,z2,z3,z4,z9,z128]),(0,[z335,z2,z3,z4,z14,z6]),(0,[z1,z167,z3,z4,z88,z6]),(0,[z1,z29,z2,z4,z244,z42]),(0,[z1,z2,z3,z14,z14,z19]),(0,[z1,z2,z3,z4,z822,z12])],[(0,[z1,z2,z168,z4,z69,z6]),(0,[z1,z2,z3,z4,z138,z19]),(0,[z1,z2,z3,z14,z352,z19]),(0,[z1,z2,z3,z14,z559,z19])],[(0,[z1,z2,z3,z4,z9,z823])],[(0,[z1,z54,z3,z4,z9,z19]),(0,[z1,z2,z3,z9,z356,z19]),(0,[z1,z60,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z337,z12]),(0,[z1,z2,z3,z14,z6,z331]),(0,[z1,z2,z3,z4,z9,z824])],[(0,[z306,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z14,z190]),(0,[z1,z825,z2,z3,z4,z9]),(0,[z1,z2,z3,z9,z14,z191]),(0,[z1,z826,z2,z3,z4,z9]),(0,[z1,z2,z3,z9,z12,z557]),(0,[z1,z2,z3,z9,z361,z19])],[(0,[z456,z2,z238,z4,z9,z6]),(0,[z1,z2,z3,z4,z12,z14])],[(0,[z1,z509,z3,z4,z390,z6]),(0,[z216,z2,z3,z4,z9,z98]),(0,[z1,z2,z3,z4,z96,z689]),(0,[z129,z2,z3,z35,z9,z6]),(0,[z1,z2,z3,z4,z9,z827]),(0,[z1,z317,z2,z3,z14,z6]),(0,[z1,z2,z3,z17,z110,z6]),(0,[z1,z2,z3,z496,z9,z19])],[(0,[z1,z294,z3,z4,z9,z181]),(0,[z28,z2,z3,z4,z9,z405]),(0,[z1,z2,z3,z4,z9,z828]),(0,[z375,z2,z3,z166,z9,z6]),(0,[z68,z1,z2,z3,z9,z291]),(0,[z1,z167,z3,z4,z9,z19])],[(0,[z2,z3,z77,z142,z14,z6]),(0,[z1,z2,z3,z4,z829,z9])],[(0,[z107,z2,z3,z36,z9,z12]),(0,[z1,z830,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z274,z33]),(0,[z1,z2,z3,z4,z831,z6])],[(0,[z1,z2,z93,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z832]),(0,[z1,z2,z3,z833,z4,z9]),(0,[z1,z2,z3,z115,z4,z17]),(0,[z45,z1,z3,z4,z156,z19]),(0,[z1,z2,z3,z4,z9,z834]),(0,[z1,z2,z4,z9,z731,z6]),(0,[z835,z2,z3,z4,z9,z19])],[(0,[z1,z2,z3,z4,z9,z836]),(0,[z1,z2,z837,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z838]),(0,[z1,z2,z751,z8,z9,z6])],[(0,[z1,z2,z839,z4,z9,z6]),(0,[z395,z1,z2,z3,z14,z19])]],
   [[(0,[z1,z2,z3,z840,z4,z6]),(0,[z1,z2,z3,z4,z9,z841]),(0,[z1,z2,z842,z4,z9,z6]),(0,[z1,z2,z109,z4,z17,z6]),(0,[z1,z46,z3,z4,z9,z499]),(0,[z1,z2,z20,z4,z9,z581])],[(0,[z2,z3,z4,z9,z186,z226]),(0,[z0,z1,z2,z3,z14,z19]),(0,[z2,z3,z4,z9,z843,z43]),(0,[z1,z2,z3,z4,z9,z844]),(0,[z1,z76,z2,z4,z131,z6])],[(0,[z126,z3,z4,z66,z9,z6]),(0,[z1,z392,z2,z3,z4,z9]),(0,[z456,z2,z343,z4,z9,z6]),(0,[z1,z2,z3,z751,z9,z6])],[(0,[z125,z752,z3,z4,z9,z6]),(0,[z1,z845,z2,z3,z4,z9]),(0,[z195,z1,z11,z4,z9,z122]),(0,[z1,z25,z3,z640,z9,z6]),(0,[z846,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z124,z14,z6]),(0,[z70,z1,z2,z751,z9,z6])],[(0,[z1,z2,z3,z847,z9,z6]),(0,[z1,z2,z3,z4,z14,z222]),(0,[z1,z2,z3,z541,z14,z6]),(0,[z1,z2,z3,z208,z9,z6]),(0,[z1,z2,z3,z4,z17,z205]),(0,[z1,z2,z3,z4,z9,z848]),(0,[z1,z2,z3,z849,z9,z6]),(0,[z1,z2,z3,z4,z39,z158]),(0,[z1,z2,z3,z104,z14,z19]),(0,[z1,z850,z3,z4,z9,z6])],[(0,[z1,z2,z3,z423,z269,z6]),(0,[z1,z2,z3,z4,z9,z401]),(0,[z1,z2,z3,z4,z9,z851]),(0,[z1,z2,z3,z391,z14,z19])],[(0,[z1,z2,z3,z4,z9,z852]),(0,[z1,z658,z2,z4,z9,z42]),(0,[z1,z2,z3,z4,z9,z853]),(0,[z1,z2,z3,z4,z854,z12])],[(0,[z1,z2,z855,z4,z9,z6]),(0,[z1,z2,z3,z4,z437,z12]),(0,[z1,z85,z3,z4,z9,z256]),(0,[z195,z1,z11,z4,z9,z19]),(0,[z1,z856,z2,z3,z4,z9]),(0,[z1,z2,z3,z110,z14,z6]),(0,[z1,z2,z13,z3,z12,z14])],[(0,[z1,z857,z3,z4,z9,z6]),(0,[z1,z34,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z858,z6]),(0,[z1,z2,z3,z4,z859,z9]),(0,[z1,z2,z3,z4,z17,z176]),(0,[z1,z2,z3,z9,z211,z19])],[(0,[z1,z2,z238,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z860]),(0,[z1,z2,z861,z4,z9,z6]),(0,[z1,z46,z3,z4,z9,z529]),(0,[z1,z2,z3,z14,z81,z19]),(0,[z1,z2,z3,z4,z9,z862])],[(0,[z49,z2,z3,z347,z9,z6]),(1,[z1,z2,z3,z14,z191]),(0,[z863,z2,z3,z4,z9,z6])],[(0,[z313,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z864,z6]),(0,[z1,z2,z3,z36,z14,z6]),(0,[z555,z2,z3,z4,z9,z186]),(0,[z1,z2,z3,z4,z14,z128]),(0,[z1,z2,z3,z156,z14,z19]),(0,[z1,z2,z3,z4,z65,z19])],[(0,[z1,z126,z3,z115,z4,z9]),(0,[z195,z218,z11,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z865]),(0,[z1,z2,z236,z4,z9,z19])],[(0,[z1,z123,z3,z4,z502,z6]),(0,[z1,z866,z3,z4,z9,z6]),(0,[z136,z2,z3,z4,z9,z240]),(0,[z1,z2,z3,z4,z867,z9]),(0,[z1,z2,z3,z4,z9,z868])],[(0,[z1,z37,z2,z3,z133,z4]),(0,[z1,z2,z3,z9,z12,z291])],[(0,[z1,z2,z3,z189,z437,z6]),(0,[z1,z2,z3,z4,z9,z869]),(0,[z1,z2,z3,z35,z234,z6]),(0,[z1,z2,z3,z241,z9,z19])]],
   [[(0,[z870,z1,z2,z3,z9,z6]),(0,[z1,z513,z2,z3,z133,z4]),(0,[z1,z2,z3,z4,z9,z871]),(0,[z1,z2,z3,z92,z279,z6])],[(0,[z1,z2,z872,z4,z9,z6]),(0,[z1,z41,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z873]),(0,[z1,z874,z3,z4,z9,z6]),(0,[z1,z2,z3,z35,z9,z176])],[(0,[z1,z2,z120,z4,z14,z6]),(0,[z1,z2,z3,z97,z9,z12]),(0,[z1,z60,z30,z4,z17,z6]),(0,[z70,z1,z2,z575,z9,z6]),(0,[z1,z2,z875,z3,z4,z9]),(0,[z1,z2,z3,z4,z876,z6])],[(0,[z153,z24,z3,z4,z9,z12]),(0,[z1,z2,z877,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z878]),(0,[z1,z2,z3,z4,z12,z138]),(0,[z1,z46,z2,z3,z9,z291]),(0,[z1,z2,z3,z4,z9,z33])],[(0,[z218,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z30,z761,z4,z9,z6]),(0,[z187,z1,z2,z3,z14,z6])],[(0,[z1,z880,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z881]),(0,[z1,z2,z120,z4,z55,z6]),(0,[z1,z2,z3,z4,z9,z882]),(0,[z129,z2,z3,z4,z9,z12])],[(0,[z23,z1,z3,z202,z9,z19]),(0,[z1,z2,z168,z4,z157,z19]),(0,[z1,z29,z2,z3,z883,z6]),(0,[z884,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z12]),(0,[z302,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z491,z336]),(0,[z1,z2,z885,z4,z9,z19])],[(0,[z28,z126,z3,z4,z9,z81]),(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z886,z9,z6]),(0,[z28,z2,z3,z4,z9,z43]),(0,[z1,z76,z2,z4,z82,z6])],[(0,[z1,z2,z3,z4,z887,z6]),(0,[z1,z41,z3,z189,z9,z6]),(0,[z1,z509,z611,z4,z9,z6]),(0,[z1,z2,z93,z142,z9,z6]),(0,[z888,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z889,z9,z6]),(0,[z1,z2,z3,z4,z234,z401]),(0,[z1,z2,z3,z9,z12,z638])],[(0,[z1,z2,z3,z551,z9,z19]),(0,[z194,z2,z3,z142,z9,z6]),(0,[z1,z2,z3,z4,z890,z6]),(0,[z1,z891,z3,z4,z9,z6]),(0,[z1,z37,z2,z3,z4,z315]),(0,[z277,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z17,z231])],[(0,[z1,z2,z3,z4,z9,z892]),(0,[z1,z2,z3,z4,z893,z6]),(0,[z1,z2,z579,z3,z14,z6]),(0,[z1,z2,z3,z4,z9,z894]),(0,[z1,z2,z3,z4,z279,z19]),(0,[z1,z271,z2,z4,z9,z435])],[(0,[z1,z2,z3,z347,z9,z895]),(0,[z1,z2,z3,z4,z9,z896])],[(0,[z41,z3,z77,z4,z9,z6]),(0,[z1,z2,z30,z4,z467,z6])],[(0,[z1,z897,z3,z4,z9,z6]),(0,[z1,z898,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z899]),(0,[z1,z900,z3,z4,z9,z6])],[(0,[z246,z1,z3,z202,z9,z6]),(0,[z1,z2,z901,z4,z9,z6]),(0,[z1,z2,z3,z189,z9,z6]),(0,[z1,z2,z3,z347,z437,z6]),(0,[z566,z2,z77,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z902]),(0,[z1,z2,z3,z4,z903,z9]),(0,[z1,z2,z3,z904,z4,z14])]],
   [[(0,[z1,z2,z3,z4,z9,z905]),(0,[z906,z2,z3,z4,z9,z6]),(0,[z1,z3,z4,z9,z730,z6]),(0,[z1,z2,z3,z237,z9,z19]),(0,[z1,z2,z3,z9,z291,z19]),(0,[z1,z37,z2,z3,z4,z225])],[(0,[z699,z2,z3,z142,z9,z6]),(0,[z1,z294,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z228,z6]),(0,[z1,z167,z3,z4,z9,z268]),(0,[z1,z2,z3,z4,z100,z6]),(0,[z1,z2,z168,z4,z469,z157])],[(0,[z1,z2,z109,z423,z9,z6]),(0,[z1,z2,z3,z4,z9,z907]),(0,[z1,z2,z3,z4,z337,z98]),(0,[z1,z2,z3,z35,z14,z19]),(0,[z1,z2,z3,z17,z768,z6])],[(0,[z1,z2,z3,z4,z908,z6]),(0,[z27,z2,z3,z142,z9,z6])],[(0,[z1,z2,z3,z4,z909,z9]),(0,[z2,z3,z4,z9,z6,z843]),(0,[z1,z2,z3,z97,z467,z6])],[(0,[z1,z2,z3,z4,z9,z910]),(0,[z1,z2,z3,z4,z9,z911]),(0,[z1,z2,z109,z4,z9,z12]),(0,[z28,z1,z2,z3,z4,z39]),(0,[z195,z1,z11,z4,z9,z240])],[(0,[z1,z2,z912,z4,z9,z6]),(0,[z612,z2,z77,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z913]),(0,[z1,z2,z3,z4,z914,z9]),(0,[z218,z2,z3,z4,z467,z6]),(0,[z1,z2,z3,z4,z9,z915]),(0,[z1,z2,z3,z4,z916,z6]),(0,[z1,z2,z3,z365,z9,z917])],[(0,[z2,z3,z142,z370,z14,z6]),(0,[z195,z1,z11,z4,z483,z6]),(0,[z918,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z14,z336]),(0,[z1,z2,z3,z4,z919,z6]),(0,[z1,z920,z2,z3,z4,z9]),(0,[z1,z94,z2,z3,z14,z6])],[(0,[z1,z24,z3,z4,z9,z255]),(0,[z0,z2,z77,z4,z9,z6]),(0,[z1,z2,z93,z4,z399,z6]),(0,[z108,z2,z109,z4,z55,z6]),(0,[z1,z2,z3,z4,z921,z6]),(0,[z1,z2,z3,z4,z922,z6])],[(0,[z1,z2,z923,z4,z9,z6]),(0,[z1,z41,z3,z347,z9,z6]),(0,[z1,z924,z2,z3,z4,z14])],[(0,[z1,z2,z3,z4,z9,z925]),(0,[z1,z926,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z234,z191]),(0,[z1,z2,z3,z9,z308,z19]),(0,[z1,z2,z3,z9,z733,z19])],[(0,[z1,z927,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z234,z12]),(0,[z1,z325,z2,z3,z4,z9])],[(0,[z1,z2,z3,z4,z928,z6]),(0,[z1,z2,z611,z4,z399,z6]),(0,[z1,z2,z929,z4,z9,z6]),(0,[z1,z25,z3,z31,z234,z6]),(0,[z1,z2,z3,z4,z157,z379]),(0,[z318,z1,z3,z4,z9,z81]),(0,[z71,z2,z3,z4,z17,z6]),(0,[z70,z1,z2,z8,z14,z6])],[(0,[z1,z2,z3,z4,z930,z6]),(0,[z1,z2,z3,z4,z931,z6]),(0,[z1,z932,z2,z3,z4,z9]),(0,[z1,z34,z3,z4,z9,z12]),(0,[z1,z2,z3,z31,z14,z19]),(0,[z375,z2,z310,z4,z9,z6]),(0,[z1,z29,z2,z595,z4,z9])],[(0,[z372,z1,z3,z4,z156,z6]),(0,[z1,z2,z3,z4,z14,z462]),(0,[z1,z509,z3,z4,z14,z6])],[(0,[z1,z2,z13,z77,z14,z6]),(0,[z1,z933,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z934])]],
   [[(0,[z1,z2,z3,z4,z9,z935]),(0,[z1,z2,z936,z4,z9,z6]),(0,[z1,z2,z3,z166,z9,z19]),(0,[z1,z937,z3,z4,z9,z6])],[(0,[z1,z2,z938,z4,z9,z6]),(0,[z1,z2,z343,z4,z9,z19]),(1,[z1,z3,z4,z730,z6]),(0,[z1,z2,z3,z4,z9,z939]),(0,[z1,z2,z3,z4,z9,z940]),(0,[z1,z2,z3,z365,z469,z9])],[(0,[z941,z2,z3,z4,z9,z6]),(0,[z1,z2,z168,z4,z157,z239]),(0,[z1,z37,z2,z3,z4,z587])],[(0,[z1,z942,z3,z4,z9,z6]),(0,[z1,z2,z373,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z943]),(0,[z1,z2,z3,z4,z944,z6]),(0,[z1,z2,z3,z62,z14,z6]),(0,[z1,z2,z3,z4,z228,z205]),(0,[z1,z2,z3,z202,z12,z14]),(0,[z1,z2,z3,z341,z14,z6])],[(0,[z1,z2,z3,z347,z709,z6]),(0,[z1,z2,z3,z189,z738,z6]),(0,[z1,z945,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z946,z6]),(0,[z1,z947,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z450]),(0,[z1,z2,z93,z36,z9,z6]),(0,[z1,z948,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z949]),(0,[z277,z2,z236,z4,z9,z6]),(0,[z45,z1,z3,z4,z156,z128]),(0,[z1,z2,z3,z18,z14,z19]),(0,[z572,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z17,z162])],[(0,[z1,z950,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z951,z6])],[(0,[z1,z60,z30,z4,z9,z12]),(0,[z1,z2,z3,z952,z4,z9])],[(0,[z1,z2,z3,z4,z14,z179]),(0,[z277,z2,z3,z241,z9,z6]),(0,[z1,z123,z3,z4,z312,z6]),(0,[z132,z2,z3,z4,z9,z405])],[(0,[z27,z34,z3,z142,z9,z6]),(0,[z1,z2,z953,z4,z9,z6]),(0,[z1,z535,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z954,z6]),(0,[z1,z46,z3,z4,z17,z135]),(0,[z955,z2,z3,z4,z9,z12])],[(0,[z313,z29,z2,z3,z4,z9]),(1,[z1,z2,z3,z14,z336]),(0,[z465,z1,z3,z4,z352,z6]),(0,[z1,z2,z3,z112,z14,z6]),(0,[z1,z2,z3,z9,z12,z733])],[(0,[z1,z2,z3,z4,z9,z956]),(0,[z440,z24,z3,z4,z9,z6]),(0,[z300,z1,z3,z4,z156,z6]),(0,[z1,z141,z2,z3,z148,z6])],[(0,[z45,z1,z3,z166,z156,z6]),(0,[z1,z2,z3,z4,z17,z173]),(0,[z1,z2,z3,z4,z9,z957]),(0,[z1,z2,z3,z4,z9,z958]),(0,[z1,z2,z3,z4,z480,z63])],[(0,[z1,z2,z3,z584,z14,z6]),(0,[z1,z2,z3,z4,z9,z959]),(0,[z1,z325,z2,z3,z4,z17]),(0,[z1,z2,z3,z9,z522,z19])],[(0,[z1,z2,z3,z4,z9,z960]),(0,[z1,z2,z3,z4,z9,z379])],[(0,[z1,z2,z3,z4,z9,z961]),(0,[z1,z2,z3,z280,z9,z12]),(0,[z1,z2,z3,z208,z9,z925]),(0,[z1,z2,z3,z4,z962,z6])]],
   [[(0,[z335,z46,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z963,z6])],[(0,[z1,z2,z3,z66,z14,z6]),(0,[z1,z2,z3,z964,z9,z6])],[(0,[z1,z2,z3,z4,z9,z965]),(0,[z1,z2,z3,z189,z9,z966]),(0,[z1,z2,z83,z475,z4,z9]),(0,[z1,z46,z3,z4,z9,z134]),(0,[z1,z2,z3,z4,z17,z188])],[(0,[z1,z2,z3,z4,z9,z95]),(0,[z294,z3,z4,z9,z55,z6]),(0,[z1,z294,z3,z4,z9,z256]),(0,[z1,z2,z3,z4,z9,z98]),(1,[z129,z2,z8,z9,z6]),(0,[z70,z1,z2,z8,z88,z6])],[(0,[z1,z2,z3,z215,z9,z19]),(0,[z1,z596,z2,z3,z14,z6]),(0,[z1,z2,z236,z4,z9,z128]),(0,[z129,z2,z3,z4,z9,z336]),(0,[z1,z2,z3,z4,z967,z6]),(0,[z1,z2,z3,z4,z17,z838])],[(0,[z1,z2,z3,z4,z968,z6]),(0,[z1,z2,z3,z969,z9,z6]),(0,[z216,z2,z3,z4,z14,z6]),(0,[z1,z2,z310,z4,z14,z6]),(0,[z1,z123,z2,z3,z14,z19]),(0,[z313,z2,z3,z4,z9,z81]),(0,[z1,z2,z533,z4,z9,z103]),(0,[z1,z2,z3,z4,z39,z12])],[(0,[z1,z41,z3,z4,z14,z6]),(0,[z1,z2,z3,z365,z491,z6]),(0,[z1,z2,z970,z4,z14,z6])],[(0,[z1,z971,z3,z4,z9,z6]),(0,[z1,z2,z972,z4,z9,z6]),(0,[z1,z2,z3,z241,z9,z128])],[(0,[z153,z24,z3,z4,z14,z6]),(0,[z1,z60,z657,z4,z9,z6]),(0,[z313,z2,z3,z4,z96,z9]),(0,[z1,z2,z3,z598,z9,z19]),(0,[z1,z2,z3,z4,z96,z625])],[(0,[z1,z2,z3,z973,z9,z6]),(0,[z1,z2,z120,z4,z172,z6]),(0,[z218,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z414,z9,z19])],[(0,[z1,z2,z3,z208,z17,z6]),(0,[z1,z2,z3,z4,z974,z6]),(0,[z70,z1,z2,z8,z9,z19]),(0,[z1,z2,z3,z32,z14,z19]),(0,[z1,z554,z3,z4,z9,z331])],[(0,[z1,z2,z975,z4,z9,z6]),(0,[z1,z2,z3,z976,z9,z6]),(0,[z1,z2,z3,z977,z9,z6]),(0,[z1,z2,z3,z4,z9,z978]),(0,[z1,z2,z13,z7,z14,z6]),(0,[z1,z34,z3,z4,z9,z450]),(0,[z1,z2,z3,z14,z43,z19]),(0,[z56,z1,z3,z202,z9,z6]),(0,[z1,z2,z3,z4,z17,z401]),(0,[z1,z2,z236,z166,z9,z6])],[(0,[z1,z2,z120,z4,z9,z181]),(0,[z1,z3,z4,z964,z9,z6]),(0,[z1,z627,z3,z4,z9,z135])],[(1,[z1,z2,z3,z14,z190]),(0,[z1,z2,z3,z4,z567,z9]),(0,[z1,z2,z3,z979,z9,z6]),(0,[z1,z2,z3,z403,z9,z19]),(0,[z1,z2,z3,z4,z14,z980]),(0,[z1,z2,z3,z4,z981,z6]),(0,[z1,z2,z3,z4,z148,z19])],[(0,[z1,z2,z3,z4,z982,z6]),(0,[z1,z2,z3,z82,z14,z19]),(0,[z1,z2,z3,z9,z291,z42]),(0,[z1,z2,z3,z4,z104,z737])],[(0,[z1,z2,z3,z4,z756,z6])]],
   [[(0,[z1,z2,z3,z4,z9,z983]),(0,[z114,z2,z3,z4,z668,z6]),(0,[z1,z37,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z829,z17])],[(0,[z631,z126,z3,z4,z9,z6]),(0,[z0,z2,z77,z4,z5,z6]),(0,[z1,z984,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z985,z6]),(0,[z1,z2,z3,z151,z14,z6]),(0,[z71,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z14,z19,z331])],[(0,[z153,z24,z3,z4,z9,z226]),(0,[z1,z2,z3,z4,z9,z986]),(0,[z1,z2,z987,z4,z9,z6]),(0,[z1,z175,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z988,z6]),(0,[z1,z2,z3,z31,z12,z14]),(0,[z277,z2,z3,z4,z9,z128]),(0,[z1,z2,z3,z989,z9,z6]),(0,[z1,z513,z2,z3,z14,z19])],[(0,[z1,z2,z3,z990,z9,z6]),(0,[z1,z2,z3,z4,z9,z991]),(0,[z1,z2,z3,z4,z992,z6]),(0,[z685,z1,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z9,z993]),(0,[z1,z2,z3,z4,z469,z14]),(1,[z1,z2,z3,z4,z737])],[(0,[z335,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z994]),(0,[z1,z2,z3,z35,z9,z851])],[(0,[z1,z2,z3,z4,z995,z6]),(0,[z996,z2,z3,z4,z9,z6])],[(0,[z56,z1,z11,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z997]),(0,[z23,z1,z343,z202,z9,z6]),(0,[z1,z3,z31,z964,z9,z6]),(0,[z1,z2,z3,z9,z576,z19]),(0,[z1,z2,z3,z4,z998,z9]),(0,[z1,z2,z3,z484,z9,z12])],[(0,[z2,z93,z4,z142,z9,z6]),(0,[z1,z2,z3,z423,z9,z6]),(0,[z1,z2,z3,z36,z354,z14]),(0,[z1,z392,z2,z3,z4,z17]),(0,[z1,z11,z4,z97,z9,z6]),(0,[z1,z2,z3,z4,z999,z6]),(0,[z1,z74,z2,z3,z14,z6])],[(0,[z0,z58,z2,z77,z4,z9]),(0,[z1,z509,z93,z4,z9,z6]),(0,[z1,z3,z964,z202,z9,z6]),(0,[z1,z2,z3,z4,z9,z1000]),(0,[z1,z2,z3,z4,z104,z158])],[(0,[z1,z34,z3,z4,z9,z95]),(0,[z1,z2,z3,z4,z9,z190]),(0,[z1,z1001,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z191]),(0,[z1,z2,z3,z183,z14,z6]),(0,[z277,z2,z3,z166,z9,z6]),(0,[z1,z2,z3,z4,z9,z1002]),(0,[z1,z170,z2,z3,z14,z6])],[(0,[z1,z2,z3,z4,z9,z1003]),(0,[z1,z2,z3,z4,z390,z6]),(0,[z1,z2,z109,z4,z14,z6]),(0,[z1,z1004,z3,z4,z9,z6])],[(0,[z1,z2,z3,z380,z541,z6]),(0,[z1,z1005,z2,z3,z4,z9]),(0,[z613,z2,z3,z4,z9,z43]),(0,[z1,z25,z3,z31,z9,z6]),(0,[z1,z167,z4,z8,z9,z6]),(0,[z1,z2,z149,z4,z9,z42])],[(0,[z1,z2,z126,z3,z14,z19]),(0,[z1,z2,z3,z4,z1006,z6]),(0,[z70,z1,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z9,z1007])],[(0,[z1,z2,z3,z4,z9,z1008]),(0,[z108,z2,z3,z4,z55,z6]),(0,[z456,z2,z3,z4,z337,z6]),(0,[z1,z2,z3,z4,z17,z12]),(0,[z1,z2,z3,z92,z96,z63])],[(0,[z1,z2,z3,z380,z9,z181]),(0,[z28,z2,z3,z4,z17,z43]),(0,[z1,z2,z3,z196,z14,z6]),(0,[z1,z3,z4,z9,z764,z135])],[(0,[z1,z126,z3,z4,z9,z379]),(0,[z1,z2,z3,z4,z1009,z9]),(0,[z1,z2,z3,z4,z399,z19]),(0,[z1,z2,z3,z4,z567,z17]),(0,[z1,z2,z3,z4,z17,z158]),(0,[z1,z2,z3,z4,z1010,z6])]],
   [[(0,[z292,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z1011,z14,z6]),(0,[z1,z2,z3,z1012,z9,z6]),(0,[z1013,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z1014]),(0,[z1,z398,z2,z3,z14,z6]),(0,[z1,z429,z3,z4,z9,z336]),(0,[z1,z2,z3,z17,z12,z19])],[(0,[z493,z126,z3,z4,z9,z6]),(0,[z1,z2,z1015,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1016])],[(0,[z1,z2,z3,z4,z1017,z6])],[(0,[z1,z175,z2,z3,z4,z17]),(0,[z68,z313,z3,z4,z9,z81]),(0,[z1,z2,z3,z124,z9,z19]),(0,[z129,z2,z3,z32,z9,z6]),(0,[z1,z61,z2,z4,z756,z6]),(0,[z1,z2,z83,z4,z314,z9]),(0,[z1,z2,z3,z91,z9,z19]),(0,[z1,z898,z3,z4,z17,z6])],[(0,[z1,z2,z3,z4,z541,z354]),(0,[z1,z1018,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z1019,z6]),(0,[z1020,z2,z3,z4,z9,z6]),(0,[z1,z2,z236,z4,z156,z6])],[(0,[z313,z2,z3,z4,z9,z43]),(0,[z1021,z2,z3,z4,z9,z6])],[(0,[z1,z85,z120,z4,z9,z6]),(0,[z1,z2,z3,z380,z14,z6]),(0,[z1,z429,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z1022,z9])],[(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z3,z4,z9,z1024]),(0,[z1,z2,z3,z4,z1025,z6]),(0,[z1,z2,z3,z166,z9,z128])],[(0,[z27,z2,z3,z142,z17,z6]),(0,[z1,z2,z3,z4,z9,z1026]),(0,[z1,z2,z3,z1027,z9,z6]),(0,[z1,z2,z3,z4,z9,z810])],[(0,[z1,z54,z3,z4,z9,z222]),(0,[z1,z2,z3,z36,z1011,z6]),(0,[z1,z2,z238,z4,z9,z19]),(0,[z1,z282,z2,z3,z14,z6]),(0,[z1,z2,z3,z9,z12,z110]),(0,[z1,z2,z3,z96,z14,z19])],[(0,[z1,z2,z3,z4,z9,z1028]),(0,[z1,z2,z3,z4,z9,z1029]),(0,[z1,z2,z3,z4,z737,z9])],[(0,[z1,z2,z3,z4,z467,z6]),(0,[z1,z2,z3,z4,z1030,z6]),(0,[z1,z60,z30,z4,z14,z6]),(0,[z1,z1031,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z394,z368]),(1,[z1,z2,z3,z9,z733])],[(0,[z28,z1,z2,z3,z14,z19]),(0,[z1,z535,z3,z4,z9,z135]),(0,[z1,z2,z3,z312,z14,z19]),(0,[z1,z2,z3,z4,z9,z1032]),(0,[z1,z2,z3,z1033,z9,z6]),(0,[z1,z74,z2,z3,z14,z176]),(0,[z1034,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z18,z65,z19]),(0,[z1,z2,z3,z471,z9,z19])],[(0,[z0,z2,z77,z4,z17,z6]),(0,[z1,z2,z3,z97,z9,z1035]),(0,[z1,z2,z3,z14,z214,z19]),(0,[z1,z2,z3,z4,z1036,z14]),(0,[z1,z2,z3,z4,z9,z1037])],[(0,[z1,z2,z1038,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z1039]),(0,[z1,z2,z3,z208,z9,z12]),(0,[z1,z2,z11,z4,z467,z6]),(0,[z1,z1040,z2,z3,z4,z9]),(0,[z45,z1,z310,z4,z156,z6])]],
   [[(0,[z153,z433,z3,z4,z9,z6]),(0,[z1,z1041,z3,z4,z9,z6]),(0,[z1,z34,z3,z4,z390,z6]),(0,[z1042,z2,z3,z4,z9,z6]),(0,[z1,z2,z718,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z1043]),(0,[z1,z2,z3,z4,z1044,z6]),(0,[z70,z1,z2,z8,z9,z268])],[(0,[z1,z2,z3,z347,z9,z6]),(0,[z1,z1045,z3,z4,z9,z6]),(0,[z1,z2,z3,z1046,z9,z6]),(0,[z1,z2,z804,z4,z17,z6])],[(0,[z1,z2,z3,z1047,z9,z6]),(0,[z1,z2,z120,z4,z9,z19]),(0,[z1,z1048,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1035]),(0,[z1,z3,z202,z200,z14,z6])],[(0,[z107,z2,z3,z36,z14,z6]),(0,[z1,z2,z3,z280,z14,z6]),(0,[z465,z1,z3,z202,z14,z6]),(0,[z1,z2,z3,z4,z9,z1049]),(0,[z1,z141,z2,z3,z279,z12])],[(0,[z1,z2,z3,z365,z9,z6])],[(0,[z313,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z1050,z6]),(0,[z1,z61,z2,z4,z82,z6]),(0,[z1,z2,z3,z143,z9,z19]),(0,[z1,z2,z3,z291,z14,z19]),(0,[z232,z2,z3,z4,z174,z6]),(0,[z1,z2,z936,z4,z17,z6]),(0,[z1,z2,z3,z4,z492,z19])],[(0,[z375,z2,z3,z4,z9,z6]),(0,[z27,z2,z3,z142,z9,z95]),(0,[z1,z37,z2,z3,z4,z607])],[(0,[z1,z2,z3,z703,z14,z6]),(0,[z1,z2,z3,z1051,z9,z6]),(0,[z637,z2,z3,z4,z9,z186]),(0,[z1,z2,z3,z4,z39,z103])],[(0,[z1,z1052,z2,z3,z4,z9]),(0,[z1,z3,z4,z9,z81,z764]),(0,[z1,z2,z3,z14,z6,z418]),(0,[z1,z2,z3,z4,z12,z274]),(0,[z1,z2,z3,z4,z1022,z17])],[(0,[z1,z2,z611,z4,z9,z6]),(0,[z1,z2,z3,z234,z14,z6])],[(0,[z1,z2,z3,z4,z17,z450]),(0,[z1,z2,z3,z4,z1053,z9]),(1,[z1,z238,z202,z9,z6])],[(0,[z152,z2,z7,z4,z9,z6]),(0,[z1,z2,z3,z12,z14,z19])],[(0,[z1,z2,z3,z1054,z9,z6])],[(0,[z456,z2,z3,z4,z9,z6]),(0,[z2,z3,z77,z347,z9,z6]),(0,[z1,z2,z3,z4,z9,z1055]),(0,[z1,z29,z535,z3,z4,z9]),(0,[z1,z429,z3,z4,z88,z6]),(0,[z1,z2,z3,z14,z591,z19])],[(0,[z1,z2,z3,z14,z186,z19]),(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1,z2,z3,z4,z9,z1057]),(0,[z1,z2,z3,z4,z1058,z6]),(0,[z1,z74,z2,z3,z14,z231]),(0,[z1059,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z2,z3,z4,z1060,z9]),(0,[z1,z2,z3,z4,z9,z1061]),(0,[z71,z2,z3,z4,z9,z336]),(0,[z1,z278,z2,z3,z4,z587])],[(0,[z1,z1062,z2,z3,z4,z9]),(0,[z1,z2,z3,z208,z467,z6]),(0,[z1,z1063,z2,z3,z4,z9]),(0,[z884,z2,z3,z4,z9,z12])],[(0,[z1,z2,z3,z4,z1064,z6]),(0,[z1,z1065,z2,z3,z4,z6]),(0,[z578,z2,z3,z142,z9,z6]),(0,[z107,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z394,z63])],[(0,[z1,z2,z3,z4,z9,z1066]),(0,[z1,z2,z3,z4,z9,z1067]),(0,[z1,z2,z3,z4,z5,z12]),(0,[z1,z1068,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z541,z6]),(0,[z1,z571,z3,z31,z9,z6])],[(0,[z1,z2,z3,z4,z17,z379]),(0,[z1,z2,z3,z4,z96,z666]),(0,[z1,z2,z3,z35,z17,z6])],[(0,[z1,z46,z3,z4,z9,z179]),(0,[z1,z2,z3,z380,z9,z19]),(0,[z1,z2,z3,z1069,z9,z6]),(0,[z1,z2,z3,z4,z1070,z9]),(0,[z1,z2,z3,z4,z14,z1071])],[(0,[z1,z2,z3,z4,z1072,z6]),(0,[z1,z1073,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1074]),(0,[z1075,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z1076,z6]),(0,[z218,z2,z3,z4,z483,z6]),(0,[z45,z1,z3,z4,z730,z6]),(0,[z1,z2,z3,z9,z1077,z6]),(0,[z1,z2,z3,z4,z9,z1078])],[(0,[z1,z2,z3,z4,z1079,z6]),(0,[z1,z2,z3,z189,z9,z881]),(0,[z1,z2,z3,z4,z9,z1080]),(0,[z1,z2,z373,z3,z4,z17]),(0,[z1,z2,z3,z745,z9,z6]),(0,[z1,z2,z1081,z3,z4,z9])],[(0,[z1,z2,z3,z4,z17,z95]),(0,[z1,z2,z3,z1082,z9,z6]),(0,[z1,z2,z3,z4,z9,z336]),(0,[z1,z2,z3,z14,z452,z19]),(0,[z1,z2,z842,z4,z17,z6])],[(0,[z1,z2,z3,z4,z9,z1083]),(0,[z1,z2,z3,z97,z14,z6]),(0,[z45,z1,z3,z4,z112,z6]),(0,[z70,z1,z167,z8,z9,z6]),(0,[z70,z1,z429,z8,z9,z6]),(0,[z1,z319,z2,z4,z82,z6])],[(0,[z1,z2,z3,z189,z5,z6]),(0,[z1,z2,z3,z9,z681,z19]),(0,[z1,z2,z1084,z4,z9,z6]),(0,[z1,z129,z2,z3,z14,z6]),(0,[z1,z2,z3,z14,z6,z176])],[(0,[z1,z2,z3,z4,z337,z19]),(0,[z1,z2,z3,z4,z228,z12])],[(0,[z1,z2,z3,z9,z1085,z6]),(0,[z1,z2,z3,z4,z1086,z6]),(0,[z129,z2,z3,z4,z14,z6]),(0,[z1,z61,z2,z3,z110,z6]),(0,[z1,z2,z3,z119,z14,z6]),(0,[z1,z2,z3,z4,z1087,z6]),(0,[z1,z141,z2,z3,z9,z733])],[(0,[z27,z2,z3,z142,z390,z6]),(0,[z27,z2,z3,z142,z9,z12]),(0,[z1,z2,z3,z9,z14,z19]),(0,[z1,z21,z3,z4,z9,z529])],[(0,[z1,z2,z3,z4,z14,z6]),(0,[z1,z509,z3,z4,z9,z19]),(0,[z23,z1,z238,z202,z9,z6]),(0,[z1,z2,z536,z4,z9,z103]),(0,[z313,z2,z83,z3,z4,z9])]],
   [[(0,[z1,z1088,z3,z4,z9,z6]),(0,[z1,z34,z611,z4,z9,z6]),(0,[z654,z1,z2,z3,z14,z6]),(0,[z456,z2,z3,z4,z9,z205]),(0,[z1,z2,z1089,z4,z9,z6])],[(0,[z1,z2,z3,z348,z14,z6])],[(0,[z153,z2,z3,z142,z14,z6]),(0,[z114,z294,z3,z4,z9,z6]),(0,[z1,z2,z83,z4,z9,z103]),(0,[z1090,z2,z3,z4,z9,z6])],[(0,[z0,z2,z77,z4,z9,z12]),(0,[z161,z2,z3,z142,z14,z6]),(0,[z1,z2,z3,z115,z4,z14]),(0,[z1,z46,z3,z4,z14,z135])],[(0,[z1,z2,z109,z4,z9,z181]),(0,[z1,z2,z3,z350,z14,z6]),(0,[z313,z2,z3,z4,z17,z6])],[(0,[z1,z2,z3,z4,z1091,z6]),(0,[z1,z2,z3,z4,z1092,z6]),(0,[z1,z2,z120,z4,z9,z256]),(0,[z1,z2,z3,z4,z9,z1093]),(0,[z1,z167,z3,z8,z9,z6]),(0,[z1,z2,z3,z178,z14,z6]),(0,[z1,z2,z3,z4,z39,z63]),(0,[z1,z2,z3,z4,z96,z75])],[(0,[z1,z2,z3,z4,z1094,z6]),(0,[z1,z2,z3,z4,z1095,z9]),(0,[z1,z25,z3,z964,z9,z6]),(0,[z1,z2,z3,z4,z14,z173]),(0,[z1,z2,z3,z4,z274,z19]),(0,[z1,z2,z3,z4,z9,z1096]),(0,[z1,z2,z3,z1097,z9,z6])],[(0,[z1,z2,z3,z362,z14,z6]),(0,[z1,z2,z3,z4,z9,z1098]),(0,[z1,z11,z202,z8,z9,z6]),(0,[z1,z167,z3,z9,z14,z6]),(0,[z1,z2,z3,z4,z104,z39]),(0,[z1,z2,z717,z4,z14,z6])],[(0,[z1,z2,z3,z4,z9,z1099]),(0,[z1,z2,z3,z4,z9,z1100])],[(0,[z1,z2,z3,z4,z9,z226]),(0,[z1,z1101,z3,z4,z9,z6]),(0,[z367,z1,z2,z8,z9,z6]),(0,[z1,z2,z13,z11,z14,z6]),(0,[z68,z1,z2,z3,z4,z39])],[(0,[z1,z2,z3,z4,z9,z1102]),(0,[z1,z535,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z883,z6]),(0,[z395,z2,z3,z4,z9,z426])],[(0,[z0,z2,z77,z189,z9,z6]),(0,[z1,z2,z3,z4,z9,z727]),(0,[z1,z2,z4,z9,z731,z103]),(0,[z1,z937,z3,z4,z9,z12])],[(0,[z2,z752,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1036]),(0,[z1,z2,z3,z4,z9,z1103]),(0,[z1,z3,z31,z202,z14,z6]),(0,[z1,z2,z3,z4,z17,z33]),(0,[z1,z2,z3,z82,z291,z6]),(0,[z1,z2,z3,z4,z9,z1104]),(0,[z1,z2,z3,z4,z14,z188])],[(0,[z1,z46,z3,z4,z9,z251]),(0,[z1,z2,z3,z4,z437,z19]),(0,[z1,z2,z3,z4,z1105,z6]),(0,[z1,z2,z3,z423,z17,z6]),(0,[z70,z71,z2,z3,z14,z6]),(0,[z1,z38,z2,z3,z14,z6]),(0,[z1,z74,z2,z3,z768,z6])],[(0,[z1,z2,z3,z4,z9,z1106]),(0,[z68,z1,z2,z3,z14,z19]),(1,[z1,z167,z3,z14,z6]),(0,[z1,z2,z13,z3,z14,z6]),(0,[z1,z278,z2,z3,z14,z19])],[(0,[z1,z79,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z190]),(0,[z1,z2,z3,z4,z17,z191])]],
   [[(0,[z1,z105,z2,z3,z14,z6])],[(1,[z2,z93,z142,z9,z6]),(0,[z10,z1,z2,z3,z9,z291]),(0,[z1,z2,z3,z4,z14,z205]),(0,[z1,z2,z1107,z4,z9,z6]),(0,[z1,z2,z3,z4,z1108,z6]),(0,[z1,z1109,z3,z4,z9,z6]),(1,[z1,z2,z3,z14,z19])],[(0,[z1,z2,z3,z66,z9,z19]),(0,[z153,z680,z3,z4,z9,z6]),(0,[z1,z54,z3,z4,z437,z6]),(0,[z1110,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1111]),(0,[z1,z2,z3,z384,z14,z6]),(0,[z1,z2,z3,z92,z9,z6])],[(0,[z1,z2,z3,z4,z9,z1112]),(0,[z1,z294,z120,z4,z9,z6]),(0,[z1,z2,z3,z1113,z4,z9]),(0,[z1,z123,z3,z4,z312,z12]),(0,[z1,z2,z3,z4,z9,z1114])],[(0,[z1,z2,z3,z4,z1115,z6]),(0,[z1,z2,z3,z4,z9,z1116]),(0,[z1,z2,z3,z97,z9,z122]),(0,[z1,z2,z3,z208,z14,z6]),(0,[z1,z1117,z2,z3,z4,z9]),(0,[z129,z2,z3,z4,z88,z6])],[(0,[z1,z34,z3,z4,z14,z6]),(0,[z1,z648,z2,z3,z14,z6]),(0,[z1118,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z491,z268]),(0,[z1,z2,z3,z4,z14,z176])],[(0,[z136,z2,z3,z97,z9,z6]),(0,[z218,z2,z3,z4,z9,z122]),(0,[z1,z2,z3,z97,z1119,z6]),(0,[z216,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z1120]),(0,[z1,z2,z310,z4,z9,z19]),(0,[z1,z2,z1121,z3,z4,z9]),(0,[z1,z2,z3,z4,z88,z6]),(0,[z1,z164,z2,z3,z133,z4])],[(0,[z22,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z1122,z6]),(0,[z1,z41,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z1123]),(0,[z1,z2,z3,z380,z9,z256]),(0,[z1,z2,z3,z4,z1124,z6])],[(0,[z1,z2,z3,z189,z17,z6]),(0,[z1,z2,z3,z423,z9,z832]),(0,[z1,z2,z3,z35,z9,z191]),(0,[z1125,z2,z3,z4,z9,z6]),(0,[z1,z1126,z2,z3,z4,z9])],[(0,[z153,z24,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z9,z122]),(0,[z1,z2,z3,z4,z9,z1127]),(0,[z1,z1128,z3,z4,z9,z19])],[(0,[z125,z126,z3,z4,z9,z6]),(0,[z28,z2,z3,z4,z9,z226]),(0,[z218,z2,z3,z4,z9,z19]),(0,[z1,z601,z30,z4,z9,z6]),(0,[z1,z2,z706,z3,z14,z6])],[(0,[z136,z2,z3,z4,z9,z6]),(0,[z0,z2,z77,z347,z9,z6]),(0,[z1,z2,z3,z4,z1129,z6]),(0,[z1,z1130,z2,z3,z4,z9]),(0,[z1,z2,z3,z14,z6,z549]),(0,[z1,z2,z3,z4,z1119,z6]),(0,[z1,z2,z3,z1131,z9,z6]),(0,[z1,z2,z3,z9,z110,z19]),(0,[z1,z2,z20,z3,z14,z19])],[(0,[z1,z2,z77,z4,z5,z6]),(0,[z1,z2,z3,z4,z1132,z6]),(0,[z27,z2,z3,z142,z9,z450]),(0,[z1,z2,z3,z4,z1133,z6]),(0,[z1,z2,z3,z410,z17,z6]),(0,[z1,z429,z3,z4,z9,z268])],[],[(0,[z1,z2,z3,z4,z390,z95]),(0,[z1134,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1135]),(0,[z1136,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z1137]),(0,[z1,z85,z109,z4,z9,z6]),(0,[z1,z2,z3,z14,z557,z6]),(0,[z1,z2,z3,z4,z9,z1138]),(0,[z1,z2,z3,z18,z148,z19])]],
   [[(0,[z1,z1139,z2,z3,z4,z9]),(0,[z1,z2,z1140,z4,z9,z6]),(0,[z1,z2,z3,z14,z103,z19])],[(0,[z23,z1,z3,z202,z337,z6]),(0,[z1,z1141,z2,z3,z4,z9])],[(0,[z1,z54,z3,z4,z9,z6]),(0,[z1,z2,z3,z380,z9,z1142]),(0,[z1,z46,z2,z3,z4,z39]),(0,[z1,z2,z3,z4,z471,z104])],[(0,[z108,z392,z2,z3,z4,z55]),(0,[z1143,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1144]),(0,[z1,z2,z3,z133,z9,z19])],[(0,[z1,z1145,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z1146,z6]),(0,[z1,z2,z3,z208,z1006,z6]),(0,[z1,z25,z3,z31,z9,z401]),(0,[z1,z2,z167,z8,z9,z6]),(0,[z1,z2,z3,z4,z17,z1037])],[(0,[z1,z294,z3,z380,z9,z6]),(0,[z1,z2,z3,z257,z14,z6]),(0,[z1147,z2,z3,z4,z9,z6]),(0,[z23,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z1148,z9,z6]),(0,[z1,z2,z3,z522,z14,z6])],[(0,[z1,z2,z3,z1149,z9,z6]),(0,[z1,z2,z3,z4,z1150,z6]),(0,[z1,z2,z718,z4,z17,z6])],[(0,[z1,z2,z1151,z4,z9,z6]),(0,[z195,z1,z761,z4,z9,z6]),(0,[z1,z2,z3,z1152,z4,z9]),(0,[z1,z46,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z14,z231])],[(0,[z1,z2,z1153,z4,z9,z6]),(0,[z1,z2,z3,z347,z17,z6]),(0,[z1,z2,z3,z36,z14,z190]),(0,[z1,z2,z3,z1154,z9,z6]),(0,[z1,z2,z3,z4,z228,z98]),(0,[z537,z1,z2,z3,z14,z6]),(0,[z1,z2,z772,z4,z14,z6])],[(0,[z1,z2,z93,z4,z9,z6]),(0,[z835,z2,z3,z4,z9,z6]),(0,[z45,z1,z3,z4,z156,z6]),(0,[z1,z2,z3,z4,z14,z158]),(0,[z1,z2,z3,z9,z178,z19]),(0,[z1,z2,z3,z14,z19,z75])],[(0,[z1,z642,z2,z4,z82,z6]),(0,[z1,z2,z3,z4,z1155,z6]),(0,[z1,z2,z3,z4,z9,z1156]),(0,[z68,z1,z3,z4,z9,z81]),(0,[z1,z2,z3,z4,z9,z764])],[(0,[z1,z2,z3,z4,z1157,z6]),(0,[z612,z1,z2,z3,z14,z6]),(0,[z1,z2,z109,z4,z9,z19]),(0,[z1,z2,z3,z55,z110,z6]),(0,[z1,z1158,z2,z3,z4,z9]),(0,[z1,z2,z168,z4,z391,z6]),(0,[z572,z1,z3,z4,z9,z452])],[(0,[z153,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z1159,z6]),(0,[z1,z85,z3,z380,z9,z6]),(0,[z1,z2,z3,z4,z14,z896])],[(1,[z1,z761,z4,z9,z6]),(0,[z375,z2,z3,z4,z17,z6]),(0,[z1160,z2,z3,z4,z9,z6]),(0,[z161,z1,z2,z3,z14,z19])],[(0,[z1,z1161,z3,z4,z9,z6])],[(0,[z1,z2,z3,z1162,z9,z6]),(0,[z1,z199,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z1163,z9])]],
   [[(0,[z1,z2,z3,z4,z9,z1164]),(0,[z45,z1,z3,z4,z156,z173])],[(0,[z1,z473,z2,z4,z82,z6]),(0,[z1,z2,z3,z4,z234,z19]),(0,[z375,z2,z3,z4,z9,z173]),(0,[z1,z2,z3,z4,z491,z19]),(0,[z1,z1165,z3,z4,z9,z6])],[(0,[z1,z2,z3,z423,z9,z12]),(0,[z1,z2,z238,z4,z337,z6]),(0,[z160,z1,z2,z8,z9,z6]),(0,[z1,z141,z2,z3,z14,z19]),(0,[z1,z2,z3,z148,z6,z19])],[(0,[z1,z2,z3,z4,z9,z1166])],[(1,[z1,z11,z97,z9,z6]),(0,[z456,z3,z4,z202,z9,z6]),(0,[z456,z2,z3,z4,z17,z6]),(0,[z1,z2,z310,z241,z9,z6]),(0,[z1,z1167,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z211,z63])],[(0,[z1,z2,z3,z4,z390,z12]),(0,[z108,z2,z3,z423,z55,z6]),(0,[z1,z2,z3,z4,z17,z958]),(0,[z1,z2,z3,z4,z394,z361])],[(0,[z1,z2,z3,z97,z9,z240]),(0,[z1,z25,z3,z31,z9,z12])],[(0,[z1,z1168,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z65,z6]),(0,[z1,z2,z3,z35,z17,z162])],[(0,[z0,z2,z77,z4,z14,z6]),(0,[z108,z2,z3,z4,z55,z12]),(0,[z218,z2,z3,z4,z9,z240]),(0,[z1,z2,z3,z97,z483,z6]),(0,[z1,z2,z3,z4,z9,z1169]),(0,[z1,z2,z236,z4,z9,z6]),(0,[z1,z429,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z1170,z6])],[(0,[z1,z2,z3,z1171,z9,z6]),(0,[z1,z2,z3,z4,z9,z181]),(0,[z1,z2,z3,z4,z9,z1172]),(0,[z1,z2,z3,z4,z9,z1173]),(0,[z71,z2,z3,z4,z14,z6])],[(0,[z1,z2,z3,z202,z14,z6]),(0,[z1,z167,z3,z4,z491,z6]),(0,[z1,z2,z3,z4,z12,z148])],[(0,[z153,z24,z3,z4,z9,z255]),(0,[z1,z2,z3,z4,z9,z1174]),(0,[z1,z2,z400,z3,z14,z6]),(0,[z1175,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z241,z9,z6]),(0,[z1,z2,z3,z4,z100,z33]),(0,[z1,z2,z3,z4,z1176,z9])],[(0,[z1,z2,z3,z4,z9,z1177]),(0,[z1,z1178,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z1179,z6]),(0,[z1,z2,z343,z4,z337,z6]),(0,[z1,z2,z3,z4,z17,z98]),(0,[z1,z2,z3,z166,z156,z6]),(0,[z1,z76,z2,z13,z14,z6]),(0,[z1,z2,z3,z4,z17,z1074])],[(0,[z1,z2,z3,z189,z9,z12]),(0,[z1,z2,z3,z4,z9,z1180]),(0,[z1,z2,z3,z4,z483,z6]),(0,[z1,z60,z30,z4,z9,z19]),(0,[z1,z2,z3,z4,z521,z63])],[(0,[z1,z2,z3,z4,z9,z1181]),(0,[z1,z2,z3,z4,z1182,z6]),(0,[z1,z2,z7,z3,z14,z19]),(0,[z1,z1183,z3,z4,z9,z6]),(0,[z1,z29,z2,z4,z9,z42]),(0,[z1,z2,z3,z484,z14,z6]),(0,[z1,z583,z2,z3,z14,z6])],[(0,[z1,z2,z3,z4,z9,z255]),(0,[z1,z34,z93,z4,z9,z6]),(0,[z1,z2,z3,z486,z14,z6]),(0,[z277,z2,z310,z4,z9,z6]),(0,[z1,z2,z236,z4,z9,z173]),(0,[z1,z2,z3,z4,z9,z1184]),(0,[z1,z2,z3,z4,z17,z336]),(0,[z1,z2,z3,z4,z100,z12]),(0,[z1,z2,z3,z4,z9,z1185]),(0,[z1,z141,z2,z3,z492,z12])]],
   [[(0,[z1,z2,z3,z491,z14,z6]),(0,[z1,z2,z3,z4,z9,z1186])],[(0,[z1,z2,z3,z4,z289,z190]),(0,[z1,z2,z3,z4,z1187,z6]),(0,[z1,z2,z3,z4,z244,z6]),(0,[z1,z2,z3,z4,z14,z940])],[(0,[z1,z2,z3,z4,z9,z1188]),(0,[z1,z2,z3,z35,z541,z6]),(0,[z129,z2,z3,z4,z9,z268]),(0,[z1,z2,z168,z4,z157,z6])],[(0,[z1,z2,z1189,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1190]),(0,[z1,z2,z3,z4,z9,z1191]),(0,[z1,z2,z3,z257,z9,z19]),(0,[z456,z25,z3,z4,z9,z6]),(0,[z1,z2,z1192,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1193])],[(0,[z1,z2,z3,z4,z354,z289]),(0,[z1,z2,z3,z97,z1194,z6]),(0,[z1,z2,z3,z640,z14,z6]),(0,[z1,z2,z3,z1195,z9,z6]),(0,[z1,z2,z3,z4,z9,z268]),(0,[z1,z2,z3,z1196,z4,z9])],[(0,[z1,z2,z1197,z4,z9,z6]),(0,[z1,z2,z3,z501,z14,z6]),(0,[z1,z2,z1198,z3,z4,z9]),(0,[z1,z2,z3,z4,z768,z6])],[(0,[z1,z2,z3,z4,z9,z1199]),(0,[z153,z2,z373,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z1200]),(0,[z23,z456,z3,z202,z9,z6]),(0,[z1,z2,z3,z4,z96,z158])],[(0,[z699,z1,z2,z8,z9,z6]),(0,[z1,z1201,z3,z4,z9,z6]),(0,[z1,z2,z3,z172,z110,z6]),(0,[z1,z2,z3,z4,z467,z12]),(0,[z1,z2,z168,z3,z14,z19]),(0,[z1,z2,z3,z4,z279,z6])],[(0,[z1,z2,z3,z35,z9,z336]),(0,[z1,z2,z83,z4,z17,z103]),(0,[z1,z271,z2,z4,z9,z42])],[(0,[z1,z2,z236,z4,z312,z6]),(0,[z1,z2,z1202,z4,z9,z6])],[(0,[z1,z1203,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1142]),(0,[z375,z3,z4,z9,z156,z6]),(0,[z1,z2,z3,z4,z1204,z6]),(0,[z1,z2,z3,z4,z1205,z6]),(0,[z1,z2,z3,z4,z9,z40])],[(0,[z1,z2,z3,z4,z9,z1206]),(0,[z1,z2,z3,z4,z354,z14])],[(0,[z216,z2,z238,z4,z9,z6]),(0,[z1207,z2,z3,z4,z9,z6]),(0,[z1,z1208,z3,z4,z9,z6]),(0,[z1,z37,z2,z3,z4,z163]),(0,[z1,z2,z3,z4,z291,z63])],[(0,[z1,z294,z3,z4,z9,z6]),(0,[z1,z2,z3,z347,z9,z12]),(0,[z1,z2,z3,z4,z437,z127]),(0,[z1,z2,z109,z4,z9,z256]),(0,[z1,z2,z3,z15,z17,z6]),(0,[z1,z2,z3,z17,z14,z19]),(0,[z1,z2,z3,z4,z162,z14])],[(0,[z1,z2,z3,z347,z5,z6]),(0,[z1,z2,z3,z4,z9,z1209]),(0,[z1,z2,z3,z4,z9,z1210]),(0,[z195,z1,z2,z3,z14,z19]),(0,[z1,z2,z1211,z4,z9,z6]),(0,[z1,z2,z310,z4,z9,z128]),(0,[z1,z1212,z2,z3,z4,z9]),(0,[z1,z2,z3,z469,z9,z110])],[(0,[z1,z2,z3,z4,z17,z226]),(0,[z1,z58,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z1213]),(0,[z1,z2,z3,z241,z234,z6]),(0,[z1214,z2,z3,z4,z9,z6])]],
   [[(0,[z1,z24,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z9,z1215]),(0,[z1216,z2,z3,z4,z9,z6]),(0,[z71,z2,z3,z4,z88,z6]),(0,[z1,z2,z3,z365,z9,z12]),(0,[z1,z2,z3,z14,z6,z591])],[(0,[z1,z2,z3,z580,z14,z6]),(0,[z1,z61,z2,z4,z82,z12]),(0,[z1,z37,z2,z3,z291,z6])],[(0,[z126,z3,z4,z9,z667,z6]),(0,[z2,z126,z3,z4,z9,z462]),(0,[z1,z1217,z3,z4,z9,z6]),(0,[z1,z1218,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1219]),(0,[z1,z2,z3,z4,z1220,z6]),(0,[z1221,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z208,z483,z6]),(0,[z375,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z1222,z9,z6]),(0,[z1,z2,z3,z365,z9,z158])],[(0,[z1,z2,z3,z4,z1223,z6]),(0,[z1,z2,z3,z4,z390,z450]),(0,[z1,z2,z3,z4,z14,z95]),(0,[z1,z2,z3,z4,z1224,z6])],[(0,[z1,z85,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z1225,z6]),(0,[z28,z2,z3,z4,z9,z339]),(0,[z300,z1,z11,z4,z9,z6])],[(0,[z1,z2,z611,z4,z9,z12]),(0,[z1,z2,z310,z166,z9,z6]),(0,[z68,z1,z679,z3,z4,z9]),(0,[z1,z2,z3,z92,z9,z162])],[(0,[z1,z1226,z3,z4,z9,z6]),(0,[z216,z2,z343,z4,z9,z6]),(0,[z1,z2,z3,z4,z1227,z6]),(0,[z1,z330,z3,z4,z200,z6]),(0,[z1,z2,z3,z279,z14,z6]),(0,[z1,z2,z3,z9,z733,z6])],[(0,[z1,z41,z3,z4,z9,z127]),(0,[z2,z3,z1228,z4,z9,z6]),(0,[z1,z2,z3,z1229,z9,z6]),(0,[z1,z2,z3,z4,z9,z1230]),(0,[z1,z2,z3,z4,z9,z1231]),(0,[z71,z2,z3,z4,z9,z19]),(0,[z1,z2,z3,z4,z1232,z6]),(0,[z1,z554,z2,z3,z14,z19])],[(0,[z1,z2,z3,z92,z17,z6])],[(0,[z1,z2,z3,z4,z1233,z6]),(0,[z1,z2,z3,z4,z9,z1234]),(0,[z456,z2,z3,z4,z9,z12]),(0,[z1,z2,z3,z31,z14,z6])],[(0,[z1,z2,z3,z4,z1235,z6]),(0,[z1,z2,z3,z1236,z9,z6]),(0,[z1,z2,z3,z4,z9,z1237])],[(0,[z1,z126,z3,z202,z14,z6]),(0,[z1,z2,z3,z4,z9,z1238]),(0,[z1,z2,z3,z35,z9,z190]),(0,[z1,z294,z109,z4,z9,z6]),(0,[z1,z2,z3,z97,z9,z19]),(0,[z1,z61,z2,z4,z424,z6])],[(0,[z1,z2,z3,z4,z9,z1239])],[(0,[z1,z2,z3,z4,z9,z127]),(0,[z1,z392,z2,z3,z4,z14]),(0,[z1,z2,z3,z4,z9,z763])],[(0,[z1,z2,z3,z4,z1011,z6]),(0,[z1,z2,z3,z4,z541,z12]),(0,[z207,z2,z3,z4,z9,z43]),(0,[z1,z2,z3,z4,z9,z1240]),(0,[z313,z2,z3,z4,z14,z6]),(0,[z129,z2,z3,z4,z9,z19])],[(0,[z1,z2,z3,z4,z1241,z9]),(0,[z1,z2,z3,z4,z9,z1242]),(0,[z1,z2,z3,z4,z9,z322]),(0,[z1,z2,z3,z35,z17,z12])]],
   [[(0,[z1,z2,z3,z4,z9,z19]),(0,[z153,z2,z3,z4,z567,z9]),(0,[z1,z1243,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1244]),(0,[z1,z2,z3,z4,z1245,z6]),(0,[z71,z167,z3,z4,z9,z6]),(0,[z70,z1,z2,z3,z1246,z6]),(0,[z1,z2,z3,z4,z9,z1247])],[(0,[z1,z58,z2,z3,z4,z17]),(0,[z1,z2,z3,z4,z9,z1248]),(0,[z27,z2,z611,z142,z9,z6]),(0,[z108,z2,z3,z4,z174,z6]),(0,[z1,z2,z3,z4,z1249,z6]),(0,[z136,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z9,z1250,z6]),(0,[z1,z2,z3,z4,z1251,z6]),(0,[z1,z2,z3,z4,z9,z1252])],[(0,[z375,z123,z3,z4,z9,z6]),(0,[z1,z2,z3,z133,z9,z291])],[(0,[z28,z79,z3,z4,z9,z6]),(0,[z456,z2,z3,z4,z228,z6]),(0,[z1,z2,z3,z4,z138,z6]),(0,[z465,z1,z3,z4,z156,z6]),(0,[z1,z2,z3,z4,z1253,z6]),(0,[z1,z2,z3,z4,z14,z871])],[],[(0,[z1,z2,z3,z4,z1254,z6]),(0,[z246,z2,z3,z142,z9,z6]),(0,[z1,z2,z3,z142,z274,z6]),(0,[z420,z1,z2,z3,z14,z19])],[(0,[z125,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z9,z1255]),(0,[z1,z60,z3,z202,z14,z6]),(0,[z70,z1,z2,z3,z14,z336]),(0,[z1,z2,z3,z4,z14,z33])],[(0,[z1,z2,z3,z423,z14,z6]),(0,[z129,z167,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z1256,z6]),(0,[z1,z2,z3,z9,z162,z19])],[(0,[z206,z126,z3,z4,z9,z6]),(0,[z313,z2,z3,z4,z9,z226]),(0,[z1,z54,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z1257]),(0,[z1,z29,z2,z4,z9,z625]),(0,[z1,z2,z3,z4,z14,z882])],[(0,[z1,z2,z3,z1258,z9,z6]),(0,[z1,z2,z3,z4,z1259,z6]),(0,[z1,z167,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1260]),(0,[z1,z2,z3,z4,z14,z191])],[(0,[z1,z2,z3,z4,z1261,z9]),(0,[z1,z2,z3,z1262,z9,z6]),(0,[z1,z175,z2,z3,z4,z14]),(0,[z1,z2,z3,z4,z157,z239])],[(0,[z28,z2,z3,z4,z14,z43]),(0,[z1,z2,z13,z30,z14,z6]),(0,[z1,z2,z3,z4,z1263,z6]),(0,[z1,z2,z3,z428,z14,z6]),(0,[z1,z2,z3,z326,z14,z6]),(0,[z1,z2,z210,z4,z391,z6]),(0,[z1,z2,z3,z587,z14,z19]),(0,[z1,z2,z3,z4,z721,z19])],[(0,[z24,z752,z3,z4,z9,z6]),(0,[z1,z1264,z3,z4,z9,z6]),(0,[z1,z29,z2,z4,z39,z42])],[(0,[z1,z2,z1265,z4,z9,z6]),(0,[z1,z2,z3,z4,z1266,z6]),(0,[z1,z2,z1267,z3,z4,z9]),(0,[z1,z509,z3,z4,z399,z6]),(0,[z1,z2,z3,z166,z312,z6]),(0,[z1,z38,z2,z3,z110,z6]),(0,[z1,z1126,z2,z3,z4,z17])],[(0,[z108,z2,z3,z4,z567,z55]),(0,[z160,z1,z11,z4,z9,z6]),(0,[z1,z2,z3,z1268,z4,z9]),(0,[z216,z2,z3,z4,z337,z6]),(0,[z1,z2,z3,z365,z17,z6]),(0,[z1,z2,z3,z4,z14,z894])],[(0,[z1,z535,z3,z4,z9,z179]),(0,[z1,z2,z663,z3,z14,z6]),(0,[z1,z2,z93,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z1269]),(0,[z70,z129,z2,z8,z9,z6])]],
   [[(0,[z68,z1,z3,z4,z17,z81])],[(0,[z1,z24,z3,z115,z4,z9]),(0,[z195,z1,z11,z97,z9,z6]),(0,[z1,z2,z3,z208,z9,z122]),(0,[z195,z1,z175,z11,z4,z9]),(1,[z1,z2,z4,z9,z731])],[(0,[z1,z2,z3,z189,z14,z6]),(0,[z1,z2,z3,z4,z1270,z6]),(0,[z1,z2,z3,z4,z9,z1271])],[(0,[z1,z2,z611,z4,z17,z6]),(0,[z1,z2,z611,z4,z9,z450]),(0,[z1,z2,z1272,z4,z9,z6]),(0,[z136,z2,z3,z208,z9,z6])],[(0,[z1,z2,z3,z9,z12,z549]),(0,[z1,z2,z13,z391,z14,z6]),(0,[z1,z37,z2,z3,z4,z104])],[(0,[z1,z2,z3,z9,z1273,z6]),(0,[z1,z2,z3,z208,z9,z19]),(0,[z1,z2,z3,z4,z1274,z6])],[(0,[z542,z24,z3,z4,z9,z6]),(0,[z1,z2,z77,z347,z9,z6]),(0,[z1,z34,z3,z4,z9,z19]),(0,[z27,z2,z3,z142,z14,z6]),(0,[z195,z1,z11,z4,z9,z6]),(0,[z1,z2,z3,z1275,z9,z6]),(0,[z1,z513,z2,z3,z4,z104])],[(0,[z1,z2,z120,z380,z9,z6]),(0,[z1,z2,z650,z4,z157,z6]),(0,[z1,z2,z3,z4,z1276,z6]),(0,[z1,z442,z2,z3,z9,z12]),(0,[z1,z2,z3,z370,z14,z19])],[(0,[z1,z2,z3,z1277,z9,z6]),(0,[z1,z25,z3,z31,z9,z191]),(0,[z1,z382,z2,z3,z4,z104]),(0,[z1,z2,z3,z9,z148,z19])],[(0,[z752,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z148,z6])],[(0,[z1,z2,z3,z1278,z9,z6]),(0,[z1,z2,z464,z4,z82,z6])],[(0,[z126,z3,z4,z9,z106,z6]),(0,[z1,z2,z3,z4,z1279,z6]),(0,[z1,z2,z1280,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z1281]),(0,[z1,z223,z2,z3,z14,z6]),(0,[z1,z2,z3,z36,z14,z19]),(0,[z2,z3,z4,z1282,z55,z6]),(0,[z195,z1,z115,z11,z4,z9]),(0,[z129,z2,z4,z8,z9,z6]),(0,[z1,z2,z3,z4,z9,z239])],[(0,[z1,z2,z93,z4,z9,z95]),(0,[z367,z1,z3,z202,z9,z6]),(0,[z1,z2,z3,z4,z9,z1283]),(0,[z1,z2,z3,z200,z14,z19]),(0,[z1,z2,z3,z92,z9,z12])],[(0,[z153,z24,z3,z4,z9,z179]),(0,[z1,z2,z3,z4,z9,z240]),(0,[z1,z2,z236,z4,z17,z6]),(0,[z71,z2,z3,z4,z9,z268])],[(0,[z490,z126,z3,z4,z9,z6]),(0,[z1,z2,z1284,z4,z9,z6]),(0,[z1,z2,z3,z4,z17,z181]),(0,[z1,z2,z3,z4,z9,z1285]),(0,[z1,z2,z3,z4,z9,z1286])]],
   [[(0,[z1,z2,z3,z4,z9,z1287])],[(0,[z1,z2,z3,z1288,z9,z6]),(0,[z1,z2,z3,z4,z437,z222]),(0,[z1,z2,z611,z4,z9,z95]),(0,[z1,z2,z3,z36,z274,z6]),(0,[z1,z2,z3,z166,z183,z6]),(0,[z1,z2,z3,z4,z88,z12]),(0,[z1,z37,z2,z3,z4,z217]),(0,[z1,z2,z710,z4,z9,z6]),(0,[z1,z2,z3,z480,z14,z19])],[(0,[z1,z2,z3,z1289,z9,z6]),(0,[z1,z2,z3,z4,z1290,z9]),(0,[z1,z2,z3,z4,z9,z1291]),(0,[z1,z2,z3,z4,z9,z256]),(0,[z1,z2,z3,z4,z9,z1292]),(0,[z1,z3,z11,z202,z14,z6]),(0,[z335,z3,z4,z9,z81,z6]),(0,[z1,z2,z48,z4,z157,z6])],[(0,[z1,z2,z4,z9,z756,z6])],[(0,[z1,z3,z4,z9,z81,z179]),(0,[z1,z2,z3,z1293,z9,z6]),(0,[z1,z535,z3,z4,z9,z186]),(0,[z1,z2,z3,z4,z9,z1294]),(0,[z1,z2,z3,z4,z322,z14]),(0,[z1295,z1,z2,z3,z4,z9]),(0,[z1,z29,z2,z4,z17,z42])],[(0,[z125,z126,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z9,z1296]),(0,[z1,z2,z3,z4,z1297,z6]),(0,[z456,z2,z3,z4,z9,z98]),(0,[z23,z1,z3,z202,z9,z6]),(0,[z1,z2,z3,z241,z9,z173]),(0,[z1,z2,z3,z174,z14,z6])],[(0,[z1,z2,z3,z1298,z9,z6]),(0,[z1,z2,z3,z4,z9,z1299]),(0,[z1,z2,z3,z4,z1300,z6]),(0,[z1,z46,z3,z4,z9,z556]),(0,[z136,z2,z3,z4,z9,z12]),(0,[z1,z325,z2,z3,z4,z14]),(0,[z1,z397,z3,z4,z312,z6]),(0,[z70,z1,z2,z13,z14,z6]),(0,[z1,z2,z3,z4,z1301,z9]),(0,[z1,z2,z4,z9,z42,z731]),(0,[z1,z2,z885,z4,z9,z6])],[(0,[z1,z2,z1302,z4,z9,z6]),(0,[z1,z629,z2,z3,z9,z12]),(0,[z1,z2,z3,z4,z9,z1303]),(0,[z1,z947,z3,z4,z14,z6]),(0,[z1,z1040,z2,z3,z4,z14]),(0,[z1,z2,z210,z3,z14,z19])],[(0,[z1,z1304,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z14,z450]),(0,[z1,z2,z1305,z3,z4,z9]),(0,[z1,z1306,z2,z3,z4,z9])],[(0,[z277,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z5,z19]),(0,[z1,z2,z3,z428,z9,z19]),(0,[z1,z2,z3,z4,z1307,z6]),(0,[z1,z2,z3,z4,z17,z1193])],[(0,[z136,z60,z3,z4,z9,z6]),(0,[z1,z2,z284,z3,z14,z6]),(0,[z70,z1,z2,z8,z491,z6]),(0,[z1,z2,z3,z4,z17,z268]),(0,[z1,z1308,z3,z4,z9,z6]),(0,[z1,z2,z149,z4,z157,z6])],[(0,[z1,z2,z3,z4,z1309,z6]),(0,[z1,z41,z3,z4,z9,z222]),(0,[z195,z1,z11,z208,z9,z6]),(0,[z1,z2,z3,z4,z1310,z6]),(0,[z1,z2,z3,z211,z14,z19]),(1,[z1,z2,z3,z148,z19]),(0,[z1,z891,z3,z4,z9,z19])],[(0,[z1,z2,z3,z4,z1311,z6]),(0,[z1,z2,z3,z517,z14,z6]),(0,[z1,z463,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z1194,z6]),(0,[z1,z2,z87,z4,z157,z6])],[(0,[z1,z54,z3,z4,z9,z12]),(0,[z1,z636,z2,z3,z4,z104]),(0,[z1,z506,z2,z4,z82,z6])],[(0,[z1,z54,z3,z4,z5,z6]),(0,[z2,z1228,z77,z4,z9,z6]),(0,[z1,z2,z373,z3,z4,z14]),(0,[z1,z2,z3,z4,z39,z19])],[(0,[z1,z2,z3,z4,z1312,z6]),(0,[z1,z2,z3,z4,z9,z1313]),(0,[z1,z1314,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1315]),(0,[z1,z2,z3,z665,z14,z6]),(0,[z1316,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z291,z6]),(0,[z1,z2,z287,z4,z9,z144])]],
   [[(0,[z1,z2,z3,z4,z1317,z6]),(0,[z1,z2,z3,z4,z9,z1318]),(0,[z277,z2,z3,z4,z9,z173]),(0,[z1,z2,z3,z104,z110,z6]),(0,[z1,z2,z3,z4,z17,z40])],[(0,[z1,z141,z2,z3,z9,z162])],[(0,[z107,z2,z93,z4,z9,z6]),(0,[z1,z2,z3,z14,z6,z190]),(0,[z1,z2,z3,z14,z6,z191]),(0,[z1,z2,z3,z237,z17,z6]),(0,[z313,z2,z3,z4,z9,z135]),(0,[z1,z2,z168,z4,z157,z188]),(0,[z1207,z2,z3,z4,z17,z6])],[(0,[z1,z2,z1319,z4,z9,z6]),(0,[z1,z294,z3,z4,z17,z6]),(0,[z1,z2,z3,z208,z9,z240])],[(0,[z1,z2,z93,z4,z9,z12]),(0,[z1,z2,z93,z4,z390,z6]),(0,[z27,z2,z3,z142,z9,z19]),(0,[z45,z1,z3,z4,z156,z12]),(0,[z1,z2,z3,z35,z768,z6])],[(0,[z1,z54,z3,z189,z9,z6]),(0,[z1,z2,z3,z4,z9,z1320]),(0,[z1,z2,z3,z4,z1321,z6]),(0,[z1,z2,z168,z4,z44,z6]),(0,[z1,z2,z3,z4,z289,z19]),(0,[z1,z2,z3,z4,z1322,z6]),(0,[z1,z2,z3,z4,z1323,z6])],[(0,[z126,z3,z212,z4,z9,z6]),(0,[z1,z752,z3,z4,z9,z6]),(0,[z0,z2,z77,z4,z9,z127]),(0,[z1,z2,z3,z4,z9,z1324]),(0,[z1,z2,z238,z4,z9,z6]),(0,[z1,z2,z3,z4,z14,z98])],[(0,[z425,z2,z77,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1325]),(0,[z23,z1,z3,z202,z9,z205]),(0,[z1,z2,z3,z156,z110,z6])],[(0,[z372,z2,z3,z4,z55,z6]),(0,[z425,z1,z11,z4,z9,z6]),(0,[z1,z2,z3,z4,z812,z6]),(0,[z1,z2,z3,z4,z1326,z6]),(0,[z1,z2,z611,z4,z390,z6]),(0,[z1,z79,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z128])],[(0,[z0,z2,z77,z4,z9,z19]),(0,[z1,z2,z3,z677,z14,z6]),(0,[z1,z281,z2,z4,z82,z6]),(0,[z1,z2,z3,z4,z14,z336])],[(0,[z1,z85,z3,z4,z17,z6]),(0,[z1,z141,z2,z3,z12,z14])],[(0,[z1,z2,z3,z1327,z9,z6]),(0,[z1,z1328,z3,z4,z9,z6]),(0,[z23,z216,z3,z202,z9,z6])],[(0,[z1,z2,z3,z1329,z9,z6]),(0,[z1330,z2,z3,z4,z9,z6])],[],[(0,[z0,z54,z77,z4,z9,z6]),(0,[z1,z2,z3,z423,z172,z6]),(0,[z1,z2,z3,z9,z1331,z6]),(0,[z1,z2,z3,z4,z737,z6])],[(0,[z1,z2,z3,z4,z9,z1332]),(0,[z1,z2,z3,z4,z9,z1333]),(0,[z1,z2,z3,z4,z1334,z6]),(0,[z1,z2,z3,z166,z9,z6]),(0,[z1,z2,z3,z4,z9,z1335]),(0,[z1,z278,z2,z3,z291,z6])]],
   [[(0,[z1,z534,z3,z4,z9,z81]),(0,[z1,z2,z3,z77,z14,z19]),(0,[z27,z2,z93,z142,z9,z6]),(0,[z27,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z541,z190]),(0,[z1,z2,z343,z4,z9,z6])],[(0,[z1,z2,z3,z4,z1336,z6]),(0,[z1,z25,z3,z592,z9,z6]),(0,[z2,z3,z36,z142,z14,z6]),(0,[z1,z2,z3,z269,z14,z6]),(0,[z1,z2,z3,z423,z9,z1172]),(0,[z1,z2,z3,z423,z9,z181]),(0,[z1,z662,z3,z4,z9,z135]),(0,[z1,z2,z3,z9,z1337,z6])],[(0,[z1,z2,z3,z4,z17,z122]),(0,[z1,z1338,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z1339]),(0,[z1,z2,z83,z4,z14,z103]),(0,[z1,z2,z3,z4,z492,z6]),(0,[z1,z2,z3,z4,z65,z12])],[(0,[z125,z126,z3,z4,z17,z6]),(0,[z1,z126,z3,z4,z9,z255]),(0,[z1,z2,z3,z1340,z9,z6]),(0,[z1,z2,z3,z4,z17,z127]),(0,[z1,z2,z3,z142,z14,z19]),(0,[z28,z2,z3,z4,z311,z9]),(0,[z1,z2,z3,z4,z1341,z6]),(0,[z1,z2,z236,z4,z9,z12]),(0,[z1,z2,z3,z225,z9,z12])],[(0,[z108,z2,z3,z4,z1282,z6]),(0,[z1,z2,z3,z4,z1342,z6]),(0,[z68,z335,z3,z4,z9,z81]),(0,[z1,z2,z3,z4,z9,z1343]),(0,[z1,z2,z3,z904,z4,z9])],[(0,[z1,z2,z3,z4,z1344,z6]),(0,[z1,z2,z3,z17,z308,z6]),(0,[z1,z2,z3,z4,z17,z322]),(0,[z1,z29,z2,z4,z9,z559])],[(0,[z161,z2,z3,z4,z55,z6]),(0,[z136,z3,z11,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1345]),(0,[z1,z2,z3,z166,z9,z173]),(0,[z1,z2,z3,z241,z9,z12]),(0,[z1,z2,z3,z4,z17,z19])],[(0,[z108,z2,z3,z4,z55,z181]),(0,[z1,z2,z3,z4,z9,z1346]),(0,[z1,z2,z3,z4,z1347,z6])],[(0,[z1,z2,z3,z4,z567,z14]),(0,[z1,z2,z3,z4,z483,z12]),(0,[z1,z2,z238,z4,z9,z205])],[(0,[z1,z2,z3,z4,z14,z226]),(0,[z1,z123,z3,z4,z312,z19]),(0,[z1,z2,z3,z4,z1348,z6])],[(0,[z290,z1,z11,z4,z9,z6]),(0,[z45,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z104,z676]),(0,[z1,z2,z3,z585,z14,z6])],[(0,[z1,z2,z3,z441,z14,z6]),(0,[z313,z37,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z1349])],[(0,[z1,z2,z3,z4,z1350,z6]),(0,[z1,z1351,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z14,z190]),(0,[z1352,z2,z3,z4,z9,z6]),(0,[z1,z123,z3,z4,z200,z6]),(0,[z1,z167,z13,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1353]),(0,[z1,z2,z3,z4,z244,z12])],[(0,[z1,z1354,z3,z4,z9,z6]),(0,[z1,z2,z3,z423,z55,z6]),(0,[z1,z2,z3,z4,z567,z82])],[(0,[z49,z41,z3,z4,z9,z6]),(0,[z1,z924,z2,z3,z4,z9]),(0,[z1,z25,z3,z31,z14,z6]),(0,[z1,z2,z3,z4,z9,z1355])],[(0,[z1,z2,z3,z720,z14,z6]),(0,[z1,z167,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z9,z1356]),(0,[z1,z2,z168,z4,z157,z158]),(0,[z1,z2,z3,z35,z9,z19])]],
   [[(0,[z685,z1,z2,z8,z9,z6]),(0,[z10,z1,z2,z3,z4,z39]),(0,[z1,z2,z3,z369,z9,z12]),(0,[z1,z2,z3,z64,z14,z6])],[(0,[z1,z2,z3,z4,z1357,z9]),(0,[z1,z2,z3,z4,z1358,z6]),(0,[z1,z2,z3,z768,z14,z6])],[(0,[z1,z2,z93,z4,z9,z450]),(0,[z1,z2,z343,z4,z9,z205]),(0,[z1,z2,z3,z4,z9,z1359])],[],[(0,[z1,z2,z3,z4,z9,z749]),(0,[z1,z2,z3,z86,z14,z6]),(0,[z1,z2,z3,z17,z356,z6]),(0,[z1,z2,z3,z97,z9,z1360]),(0,[z1361,z2,z3,z4,z9,z6])],[(0,[z421,z2,z77,z4,z9,z6]),(0,[z10,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z17,z12,z14])],[(0,[z1,z2,z3,z312,z110,z6]),(0,[z129,z2,z3,z8,z9,z6])],[(0,[z153,z24,z3,z4,z9,z462]),(0,[z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z3,z99,z14,z6]),(0,[z1,z711,z3,z4,z9,z6])],[(0,[z1,z294,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z337,z6]),(0,[z129,z2,z3,z9,z14,z6]),(0,[z1,z167,z3,z35,z9,z6]),(0,[z1,z2,z3,z365,z9,z957])],[(0,[z1,z2,z3,z4,z9,z1360]),(0,[z455,z1,z3,z202,z9,z6]),(0,[z1,z2,z3,z4,z1362,z6]),(0,[z70,z1,z2,z8,z9,z6]),(0,[z1,z141,z2,z3,z9,z12])],[(0,[z1,z2,z1363,z4,z9,z6]),(0,[z1,z2,z3,z4,z1364,z6])],[(0,[z1,z2,z3,z4,z9,z462]),(0,[z1,z509,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z1365,z6]),(0,[z1,z2,z3,z1366,z4,z9]),(0,[z1,z761,z11,z4,z9,z6])],[(0,[z193,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z1367,z6]),(0,[z1,z85,z3,z423,z9,z6]),(0,[z1,z629,z2,z3,z14,z6]),(0,[z195,z1,z11,z4,z17,z6]),(0,[z1,z2,z3,z4,z39,z42])],[(0,[z1,z79,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z1368,z9])],[(0,[z1,z2,z3,z1369,z9,z6]),(0,[z1,z2,z3,z4,z1370,z6]),(0,[z1,z2,z3,z4,z1371,z6])],[(0,[z153,z253,z3,z4,z9,z6]),(0,[z1,z85,z3,z4,z9,z12]),(0,[z1,z2,z109,z380,z9,z6]),(0,[z313,z2,z3,z4,z9,z19]),(0,[z1,z1372,z3,z4,z9,z6]),(0,[z1,z29,z2,z3,z14,z19])]],
   [[(0,[z1,z2,z3,z1373,z9,z6]),(0,[z1,z2,z30,z3,z14,z19]),(0,[z1034,z2,z3,z4,z14,z6])],[(0,[z1,z2,z1280,z4,z17,z6]),(0,[z1,z2,z3,z4,z96,z368])],[(0,[z108,z85,z3,z4,z55,z6]),(0,[z1,z304,z3,z4,z9,z81]),(0,[z1,z2,z3,z14,z6,z336]),(0,[z1,z2,z3,z4,z17,z239]),(0,[z1,z2,z3,z18,z9,z19])],[(0,[z335,z2,z3,z4,z9,z6]),(0,[z1,z41,z3,z4,z437,z6]),(0,[z1,z2,z3,z9,z1374,z6]),(0,[z1,z411,z2,z3,z9,z12])],[(0,[z1,z2,z3,z4,z9,z1375]),(0,[z1,z24,z3,z4,z9,z379]),(0,[z1,z2,z3,z4,z17,z240]),(0,[z1,z2,z3,z241,z17,z6]),(0,[z1,z2,z197,z3,z14,z6]),(0,[z1,z2,z3,z946,z14,z6])],[(0,[z1,z2,z3,z4,z9,z179]),(0,[z1,z2,z3,z347,z14,z6]),(0,[z1,z2,z3,z296,z14,z6]),(0,[z1,z2,z3,z357,z14,z6]),(0,[z1376,z2,z3,z4,z9,z6]),(0,[z1,z429,z3,z4,z491,z6]),(0,[z1,z2,z3,z39,z883,z6])],[(0,[z1,z535,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z895]),(0,[z1377,z2,z3,z4,z9,z6]),(1,[z129,z2,z3,z14,z6]),(0,[z1,z1378,z3,z4,z9,z6]),(0,[z1,z76,z2,z3,z14,z19])],[(0,[z0,z2,z1228,z4,z9,z6]),(0,[z1,z2,z1379,z4,z9,z6]),(0,[z1,z2,z3,z166,z9,z769])],[(0,[z1,z2,z3,z4,z17,z255]),(0,[z1,z2,z3,z142,z12,z14]),(0,[z1,z482,z2,z3,z14,z6]),(0,[z1,z2,z3,z423,z9,z19]),(0,[z1,z2,z3,z4,z17,z256]),(0,[z1,z2,z30,z97,z9,z6]),(0,[z1,z2,z3,z4,z1380,z6]),(0,[z1,z2,z3,z365,z14,z6]),(0,[z1,z74,z2,z3,z14,z19])],[(0,[z1,z2,z3,z4,z1381,z6]),(0,[z1,z2,z3,z4,z5,z127]),(0,[z1,z2,z3,z4,z1382,z6]),(0,[z1,z2,z3,z4,z9,z1383]),(0,[z1,z2,z3,z4,z9,z1384])],[(0,[z1,z1385,z2,z3,z4,z9]),(0,[z1,z29,z2,z644,z4,z9]),(0,[z1,z2,z3,z4,z337,z205]),(0,[z375,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z730,z6]),(0,[z70,z1,z167,z3,z14,z6]),(0,[z1,z2,z3,z4,z1386,z6])],[(0,[z1,z2,z3,z4,z9,z1387]),(0,[z1,z2,z3,z4,z390,z19]),(1,[z1,z3,z964,z9,z6]),(0,[z23,z1,z3,z202,z17,z6]),(0,[z1,z258,z2,z3,z4,z104]),(0,[z1,z38,z2,z4,z424,z6]),(0,[z1,z2,z3,z4,z9,z733])],[(0,[z1388,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z720,z6]),(0,[z45,z1,z325,z3,z4,z156]),(0,[z1,z2,z885,z4,z17,z6])],[(0,[z1,z2,z611,z4,z14,z6]),(0,[z1,z2,z3,z4,z138,z191]),(0,[z70,z1,z2,z3,z14,z19]),(0,[z1,z2,z3,z4,z9,z917]),(0,[z1,z2,z3,z518,z9,z12]),(0,[z1,z2,z3,z14,z6,z368])],[(0,[z1,z2,z3,z4,z1389,z6]),(0,[z1,z2,z3,z4,z399,z6]),(0,[z108,z2,z3,z4,z55,z19]),(0,[z1,z2,z3,z4,z1390,z6]),(0,[z1,z1161,z3,z4,z14,z6])],[(0,[z1,z2,z3,z4,z1391,z6]),(0,[z1,z25,z3,z31,z138,z6]),(0,[z277,z2,z3,z4,z17,z6])]],
   [[(0,[z1,z2,z3,z189,z9,z127]),(0,[z1392,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z14,z176]),(0,[z1,z2,z3,z104,z9,z291])],[(0,[z218,z2,z3,z97,z9,z6]),(0,[z1,z2,z3,z4,z9,z1393]),(0,[z456,z2,z3,z4,z14,z6]),(0,[z1,z2,z238,z202,z9,z6]),(0,[z1,z2,z3,z4,z9,z1394]),(0,[z1013,z2,z3,z4,z9,z19])],[(0,[z216,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z1395,z4,z9]),(0,[z79,z3,z4,z9,z186,z6]),(0,[z1,z2,z310,z4,z9,z6]),(0,[z1,z1396,z2,z3,z4,z9]),(0,[z70,z1,z2,z3,z274,z6])],[(0,[z1,z2,z3,z189,z9,z19]),(0,[z1,z2,z970,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z222]),(0,[z1,z2,z3,z4,z1397,z9]),(0,[z1,z167,z3,z4,z9,z12]),(0,[z1,z2,z3,z4,z100,z322])],[(0,[z1398,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z228,z19]),(0,[z1,z2,z3,z4,z100,z19]),(0,[z1,z1314,z3,z4,z17,z6])],[(0,[z1,z2,z3,z4,z9,z1399]),(0,[z1,z2,z3,z4,z1400,z9]),(0,[z1,z2,z3,z4,z1246,z6]),(0,[z1,z141,z2,z3,z946,z6]),(0,[z1,z1401,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z1402]),(0,[z1,z2,z1403,z4,z9,z6]),(0,[z1,z2,z3,z410,z9,z19]),(0,[z68,z1,z3,z4,z9,z452]),(0,[z1,z2,z3,z4,z96,z63])],[(0,[z1404,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z469,z9])],[(0,[z1,z2,z3,z4,z9,z1405]),(0,[z1,z2,z3,z4,z14,z181]),(0,[z1,z2,z3,z4,z1282,z6]),(0,[z1406,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z467,z122]),(0,[z1,z2,z3,z35,z279,z6])],[(0,[z1,z2,z3,z4,z9,z1407]),(0,[z1,z2,z3,z1408,z9,z6]),(0,[z1,z2,z3,z4,z9,z980]),(0,[z1,z2,z3,z4,z480,z75])],[(0,[z542,z2,z3,z4,z9,z186]),(0,[z136,z2,z3,z4,z467,z6]),(0,[z1,z3,z4,z730,z156,z6]),(0,[z161,z2,z3,z4,z214,z6])],[(0,[z1,z2,z238,z4,z17,z6]),(0,[z1,z2,z3,z157,z14,z19]),(0,[z1,z2,z3,z1409,z9,z6]),(0,[z1,z29,z2,z4,z9,z731])],[(0,[z1,z2,z3,z4,z9,z1410]),(0,[z1,z2,z3,z4,z9,z1411]),(0,[z1,z2,z3,z4,z1412,z9]),(0,[z1,z2,z3,z4,z467,z19]),(0,[z1,z2,z3,z4,z9,z1413]),(0,[z245,z1,z3,z4,z9,z81]),(0,[z1,z278,z2,z3,z4,z163]),(0,[z1,z2,z3,z4,z737,z96])],[(0,[z1,z2,z3,z1414,z9,z6]),(0,[z1,z2,z3,z4,z17,z128]),(0,[z1,z2,z3,z4,z9,z1415]),(0,[z1,z2,z3,z17,z291,z6])],[(0,[z1,z2,z1228,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1416]),(0,[z23,z1,z3,z964,z9,z6]),(0,[z1,z2,z3,z8,z14,z19]),(0,[z1,z2,z3,z471,z17,z6])]],
   [[(0,[z1,z2,z3,z4,z1417,z6])],[(0,[z195,z1,z11,z4,z9,z12]),(0,[z1,z61,z2,z3,z14,z19])],[(0,[z1,z2,z3,z189,z1159,z6]),(0,[z1,z2,z120,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1418])],[(0,[z1,z2,z3,z347,z9,z19]),(0,[z1,z2,z3,z4,z9,z1419]),(1,[z1,z2,z3,z14,z176])],[(0,[z1,z34,z3,z4,z399,z6]),(0,[z2,z3,z745,z142,z9,z6]),(0,[z1,z2,z3,z36,z12,z14]),(0,[z216,z2,z3,z4,z9,z205]),(0,[z1420,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1421]),(0,[z1,z2,z3,z4,z96,z438]),(0,[z465,z1,z2,z3,z14,z19])],[(0,[z669,z126,z3,z4,z9,z6]),(0,[z1422,z2,z3,z4,z9,z6]),(0,[z1,z238,z4,z202,z9,z6]),(0,[z1,z2,z3,z166,z17,z6]),(0,[z1,z2,z3,z369,z14,z6]),(0,[z1090,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z291,z14,z6])],[(0,[z1,z2,z3,z4,z9,z1423]),(0,[z1,z2,z343,z4,z17,z6]),(0,[z45,z375,z3,z4,z156,z6])],[(0,[z1,z2,z3,z4,z9,z1424]),(0,[z68,z1,z602,z3,z4,z9])],[(0,[z1,z54,z3,z347,z9,z6]),(0,[z1,z2,z3,z4,z1425,z6]),(0,[z1,z2,z3,z143,z17,z6])],[(0,[z1,z2,z3,z4,z9,z1426])],[(0,[z1,z2,z3,z423,z9,z256]),(0,[z1,z2,z3,z4,z469,z17])],[(0,[z1,z25,z238,z4,z9,z6]),(0,[z129,z2,z3,z4,z491,z6])],[(0,[z59,z126,z3,z4,z9,z6]),(0,[z1,z582,z2,z3,z14,z6])],[(0,[z1,z60,z562,z4,z9,z6]),(0,[z1,z2,z3,z1427,z9,z6]),(0,[z1,z2,z3,z14,z6,z426]),(0,[z1,z333,z2,z4,z9,z42]),(0,[z1,z2,z3,z4,z1428,z6]),(0,[z654,z1,z2,z8,z9,z6]),(0,[z1,z2,z3,z4,z234,z6]),(0,[z1,z2,z3,z4,z491,z6]),(0,[z1,z2,z168,z157,z110,z6])],[(0,[z1,z2,z3,z1429,z9,z6]),(0,[z1,z1430,z2,z3,z4,z9])],[(0,[z1,z37,z535,z3,z4,z9]),(0,[z1,z442,z2,z3,z14,z6]),(0,[z1,z2,z3,z1431,z9,z6])]],
   [[(0,[z108,z2,z3,z4,z55,z256]),(0,[z1,z2,z238,z31,z9,z6]),(0,[z23,z1,z3,z202,z9,z12]),(0,[z1,z2,z4,z756,z82,z6]),(0,[z1,z2,z168,z4,z157,z12])],[(0,[z1,z2,z3,z4,z1432,z6]),(0,[z1,z2,z3,z241,z9,z1016])],[(0,[z1,z2,z3,z4,z9,z1433]),(0,[z1,z2,z3,z4,z1434,z6]),(0,[z1,z2,z3,z4,z9,z843]),(0,[z1,z79,z3,z4,z14,z6]),(0,[z129,z429,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z1435,z6]),(0,[z195,z1,z11,z4,z467,z6]),(0,[z1,z2,z3,z202,z337,z6]),(0,[z1,z2,z3,z4,z88,z336])],[(0,[z1,z2,z3,z380,z9,z6]),(0,[z1,z2,z3,z380,z9,z1436]),(0,[z1,z2,z1437,z4,z9,z6]),(0,[z1,z2,z3,z4,z1438,z6]),(0,[z1,z429,z3,z4,z9,z6]),(0,[z277,z2,z3,z4,z9,z12]),(0,[z70,z1,z2,z3,z14,z268])],[(0,[z1,z2,z3,z4,z9,z758]),(0,[z1,z2,z3,z4,z1439,z6]),(0,[z1,z2,z3,z9,z110,z1440]),(0,[z1,z2,z3,z92,z14,z6]),(0,[z1,z2,z3,z35,z17,z19]),(0,[z1,z2,z3,z4,z279,z12])],[(0,[z2,z126,z3,z142,z14,z6]),(0,[z1,z2,z3,z4,z9,z1441]),(0,[z1,z2,z3,z96,z110,z6])],[(0,[z1,z2,z3,z1442,z9,z6]),(0,[z49,z2,z3,z142,z14,z6]),(0,[z1,z2,z3,z4,z9,z1443]),(0,[z1,z2,z3,z4,z401,z14]),(0,[z1,z2,z3,z4,z9,z1444]),(0,[z1,z2,z3,z4,z9,z1440]),(0,[z1,z2,z48,z4,z16,z6])],[(0,[z1,z294,z3,z423,z9,z6]),(0,[z1,z411,z2,z3,z14,z6]),(0,[z1,z2,z3,z14,z452,z6]),(0,[z1,z1445,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z822,z6])],[(0,[z1,z2,z3,z4,z9,z1446]),(0,[z1,z1447,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z851,z19])],[(0,[z1,z2,z3,z4,z9,z1448]),(0,[z1,z1449,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z796,z6]),(0,[z1,z2,z3,z4,z1450,z6]),(0,[z23,z1,z3,z202,z228,z6]),(0,[z1,z3,z4,z9,z764,z6]),(0,[z70,z71,z2,z8,z9,z6])],[(0,[z1,z2,z3,z208,z9,z1423]),(0,[z1,z2,z3,z4,z467,z240]),(0,[z1,z2,z3,z4,z9,z1451]),(0,[z1,z2,z3,z14,z19,z63]),(0,[z955,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z9,z966]),(0,[z1,z2,z3,z4,z14,z122]),(0,[z1,z2,z3,z4,z1452,z9]),(0,[z1,z2,z13,z32,z14,z6]),(0,[z1,z2,z3,z4,z9,z1453])],[(0,[z125,z126,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z5,z222]),(0,[z1,z1454,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1455]),(0,[z1,z461,z3,z4,z312,z6])],[(1,[z2,z77,z347,z9,z6]),(0,[z1,z2,z3,z4,z9,z1456]),(0,[z1,z1457,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z9,z354]),(0,[z108,z294,z3,z4,z55,z6]),(0,[z136,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z9,z1458]),(0,[z1,z2,z3,z414,z17,z6])],[(0,[z70,z1,z2,z8,z17,z6]),(0,[z1,z141,z2,z3,z17,z12])]],
   [[(0,[z1,z1459,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1460]),(0,[z1,z2,z3,z4,z1461,z6]),(0,[z1,z535,z3,z4,z9,z81]),(0,[z1,z2,z3,z4,z9,z1462]),(0,[z1,z2,z3,z4,z14,z19])],[(0,[z1,z509,z3,z4,z17,z6]),(0,[z2,z3,z93,z142,z9,z6]),(0,[z1,z2,z3,z4,z96,z570]),(0,[z1,z2,z238,z4,z9,z12]),(0,[z465,z1,z3,z202,z9,z6]),(0,[z1,z383,z2,z3,z14,z6])],[(0,[z27,z2,z3,z142,z399,z6]),(0,[z1,z2,z3,z4,z9,z775]),(0,[z160,z1,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z9,z1463]),(0,[z1,z123,z3,z4,z730,z6]),(0,[z1,z2,z3,z518,z14,z6])],[(0,[z1,z2,z3,z1464,z9,z6]),(0,[z1,z2,z3,z36,z390,z6]),(0,[z1,z2,z3,z4,z1465,z6]),(0,[z28,z2,z3,z4,z9,z843]),(0,[z1,z535,z3,z4,z96,z9]),(0,[z375,z2,z236,z4,z9,z6]),(0,[z1,z167,z3,z4,z9,z336]),(0,[z1466,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z1467,z6]),(0,[z1,z2,z3,z470,z9,z12]),(1,[z1,z2,z4,z756,z6])],[(0,[z1,z54,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z274,z6]),(0,[z1,z2,z3,z4,z322,z274]),(0,[z1,z2,z3,z14,z19,z426]),(0,[z1,z278,z2,z3,z4,z104])],[(0,[z1,z2,z3,z1468,z9,z6]),(0,[z1,z2,z3,z31,z14,z191]),(0,[z375,z2,z3,z241,z9,z6]),(0,[z1,z2,z83,z360,z4,z9]),(0,[z1,z2,z3,z133,z14,z19])],[(0,[z1,z2,z3,z4,z9,z1469]),(0,[z509,z3,z4,z142,z9,z6]),(0,[z421,z2,z3,z4,z55,z6])],[(0,[z1,z704,z2,z4,z82,z6]),(0,[z1,z2,z1470,z3,z4,z9]),(0,[z1,z2,z3,z15,z9,z19]),(0,[z1,z2,z3,z9,z883,z6]),(0,[z1,z2,z3,z496,z14,z6]),(0,[z1,z2,z3,z18,z17,z19])],[(0,[z1,z2,z1471,z3,z4,z9]),(0,[z335,z2,z3,z4,z17,z6]),(0,[z1,z2,z20,z4,z9,z103]),(0,[z270,z1,z2,z3,z14,z19])],[(0,[z1,z2,z3,z11,z14,z19]),(0,[z1472,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z166,z9,z12]),(0,[z1,z1445,z2,z3,z4,z17])],[(0,[z1,z2,z3,z4,z17,z179]),(0,[z1,z2,z3,z4,z9,z1473]),(0,[z1,z2,z3,z4,z9,z1474]),(0,[z1,z2,z238,z4,z228,z6]),(0,[z1,z2,z343,z4,z9,z12]),(0,[z795,z2,z3,z4,z9,z6]),(0,[z1,z2,z1475,z4,z9,z6]),(0,[z1,z2,z3,z585,z9,z19]),(0,[z1476,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z854,z6])],[(0,[z1,z2,z3,z4,z437,z6]),(0,[z1,z2,z93,z4,z14,z6]),(0,[z1,z535,z3,z4,z17,z6])],[(0,[z1,z2,z3,z4,z1477,z6]),(0,[z0,z2,z77,z4,z9,z222]),(0,[z1,z2,z3,z4,z9,z1478]),(0,[z1,z2,z3,z9,z1479,z6]),(0,[z195,z136,z11,z4,z9,z6]),(0,[z68,z1,z3,z4,z14,z81]),(0,[z70,z1,z429,z3,z14,z6]),(0,[z1,z278,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z492,z12])],[],[(0,[z27,z2,z3,z745,z9,z6]),(0,[z1,z2,z3,z55,z14,z19]),(0,[z1,z25,z3,z31,z9,z19]),(0,[z1,z2,z13,z3,z14,z19]),(0,[z1,z2,z3,z4,z17,z1384])]],
   [[],[(0,[z1,z2,z7,z347,z9,z6]),(0,[z1,z461,z3,z4,z183,z6])],[(0,[z1480,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z401,z138]),(0,[z1,z2,z3,z4,z9,z1071]),(0,[z1,z2,z3,z4,z1108,z19])],[(0,[z1,z2,z1481,z4,z9,z6]),(0,[z1,z2,z761,z4,z9,z6]),(0,[z1482,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z1483,z9,z6])],[(0,[z1,z2,z13,z3,z274,z6]),(0,[z1,z2,z83,z3,z14,z19])],[(0,[z1,z2,z3,z4,z9,z1484]),(0,[z49,z2,z353,z4,z9,z6]),(0,[z2,z3,z4,z9,z1282,z6]),(0,[z1,z1485,z2,z3,z4,z9]),(0,[z1,z2,z343,z4,z228,z6])],[(0,[z1,z41,z3,z4,z9,z6]),(0,[z1,z2,z3,z1486,z9,z6]),(0,[z1,z2,z3,z4,z9,z1487]),(0,[z1,z3,z238,z202,z9,z6]),(0,[z1488,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1489]),(0,[z1,z2,z3,z952,z9,z110])],[(0,[z1,z2,z3,z4,z9,z1490]),(0,[z68,z1,z3,z4,z9,z339]),(0,[z1,z2,z3,z97,z9,z6])],[(0,[z153,z24,z3,z4,z9,z6]),(0,[z1,z1128,z3,z4,z9,z6]),(0,[z216,z2,z3,z4,z17,z6]),(0,[z219,z1,z3,z4,z112,z6])],[(0,[z218,z2,z3,z4,z9,z6]),(0,[z415,z126,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1491]),(0,[z1492,z2,z3,z4,z9,z6]),(0,[z1493,z2,z3,z4,z9,z6])],[(0,[z1,z2,z3,z4,z17,z222]),(0,[z129,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z9,z110,z6]),(0,[z1,z2,z20,z3,z14,z6]),(0,[z1,z2,z3,z4,z96,z361])],[(0,[z615,z24,z3,z4,z9,z6]),(0,[z1,z1494,z2,z3,z4,z9]),(0,[z1,z2,z236,z4,z14,z6]),(1,[z1,z2,z3,z883,z6]),(0,[z1,z2,z3,z779,z9,z6]),(0,[z1,z2,z3,z225,z14,z6])],[(0,[z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1436]),(0,[z1,z2,z3,z4,z1495,z6]),(0,[z367,z1,z2,z3,z14,z6]),(0,[z23,z1,z3,z202,z9,z98]),(0,[z1,z2,z310,z4,z9,z173]),(0,[z1,z2,z3,z1246,z14,z6]),(0,[z1,z2,z3,z4,z14,z239])],[(0,[z1,z2,z3,z4,z9,z1496]),(0,[z1,z1497,z3,z4,z9,z6]),(0,[z1,z2,z479,z4,z9,z103]),(0,[z1,z2,z3,z4,z9,z1498]),(0,[z1,z1499,z3,z4,z9,z6])],[(0,[z1,z2,z1500,z4,z9,z6]),(1,[z752,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z9,z1501]),(0,[z1,z2,z3,z4,z14,z240]),(0,[z1,z2,z3,z4,z1502,z6]),(0,[z1,z2,z3,z241,z14,z6])],[(0,[z1,z2,z3,z145,z14,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 474) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 474).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 956).take 484) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1440).take 80) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1520)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [474, 482, 484, 80] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 77).take 85).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 162).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 245).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 328).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 416).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 497).take 15).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [77, 85, 83, 83, 88, 81, 15] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

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

end PEqualNP.Outside.L_meta_38089

theorem PEqualNP.Outside.L_meta_38089 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38089.solve