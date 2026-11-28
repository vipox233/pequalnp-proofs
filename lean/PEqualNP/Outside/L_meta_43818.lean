import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43818

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4276799624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0004861b01098549#64 ++ 0x400012186c042615#64 ++ 0x013d8e3f031f8fdf#64 ++ 0xbc04f638fc0c7e3f#64 : BitVec 256),
   (0x025030c40c643aa4#64 ++ 0x800940c3103190ea#64 ++ 0x86d271c61ce4ffff#64 ++ 0x7e1b49c7187393ff#64 : BitVec 256),
   (0x58a3816960b8d309#64 ++ 0x01628e05a582e34c#64 ++ 0x78e381f9e0f8f336#64 ++ 0xede38e07e783e3cc#64 : BitVec 256),
   (0xad03da01b700ec0e#64 ++ 0x02b40f6806dc03b0#64 ++ 0xff03fe01ff00fc3d#64 ++ 0xf3fc0ff807fc03f0#64 : BitVec 256),
   (0x37f80000dad60030#64 ++ 0x04dfe000036b5800#64 ++ 0x7ffc0001ffff0033#64 ++ 0xf5fff00007fffc00#64 : BitVec 256),
   (0x3fff6db600000000#64 ++ 0x08fffdb6d8000000#64 ++ 0xbffffffe0000000f#64 ++ 0xeafffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 10]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z1 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f8fdf 0xbc04f638fc0c7e3f

def z2 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce4ffff 0x7e1b49c7187393ff

def z3 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001ffff0033 0xf5fff00007fffc00

def z4 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xffffffffffff003f 0xfffffffffffffc00

def z5 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f8f336 0xede38e07e783e3cc

def z6 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff00fc3d 0xf3fc0ff807fc03f0

def z7 : W := mkw 0x0000800900088109 0x0000020024002204 0x0021803900188316 0xac008600e400620c

def z8 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe0000000f 0xeafffffff8000000

def z9 : W := mkw 0x58a7877b61b9d749 0x41629e1ded86e75d 0x79ff8fffe3ffffff 0xfde7fe3fff8fffff

def z10 : W := mkw 0x0004965b0d6dbfed 0xc00012596c35b6ff 0x013d8e3f1fffffff 0xbc04f638fc7fffff

def z11 : W := mkw 0x02502084084400a0 0x8009408210211002 0x00100006000400c0 0x0000400018001003

def z12 : W := mkw 0x275000009a440020 0x009d400002691000 0x7fd00001ffe40033 0xf5ff400007ff9000

def z13 : W := mkw 0x275830c49e663ab4 0x849d60c3127998ea 0x87de71c61fe7ffff 0x7e1f79c7187f9fff

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000600048fdf 0x3c0040001800123f

def z15 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8003fffe0000000c 0x0a000ffff8000000

def z16 : W := mkw 0x0004861b01098549 0x400012186c042615 0x012d8e39031b0000 0x8004b638e40c6c00

def z17 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c01ce07020 0x421b09c7007381c0

def z18 : W := mkw 0x0000100004002804 0x00000040001000a0 0x860270001c007020 0x421809c0007001c0

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x003c0000001f0002 0x0400f00000007c00

def z20 : W := mkw 0x0004041200000000 0x0000101048000000 0x013d8e3e0000000f 0xa804f638f8000000

def z21 : W := mkw 0x0250208400000000 0x0009408210000000 0x86d271c60000000f 0x6a1b49c718000000

def z22 : W := mkw 0x000010400c643aa4 0x80000041003190ea 0x001000061ce4ffff 0x3c004000187393ff

def z23 : W := mkw 0x0004861bdbdf8579 0x440012186f6f7e15 0x413d8e3fffff8fff 0xbd04f638fffffe3f

def z24 : W := mkw 0x0000820901098549 0x4000020824042615 0x013c0001031f8fd3 0xb404f000040c7e3f

def z25 : W := mkw 0x0250004008641220 0x0009400100219048 0x06d201c01ce4f337 0x7c1b4807007393cc

def z26 : W := mkw 0x0000820901098549 0x4000020824042615 0x00000001031f8fd0 0x14000000040c7e3f

def z27 : W := mkw 0x0000004000201200 0x0000000100008048 0x00d201c600e4ffff 0x7c034807180393ff

def z28 : W := mkw 0x3daf4d3200000000 0x08f6bd34c8000000 0x392d8e3800000000 0x80e4b638e0000000

def z29 : W := mkw 0x4803816960b8d309 0x01200e05a582e34c 0x400381f9e0f8f334 0x0d000e07e783e3cc

def z30 : W := mkw 0x1af331e40c643aa4 0x806bccc7903190ea 0xbef3f1fe1ce4ffff 0xfefbcfc7f87393ff

def z31 : W := mkw 0x0000820101008408 0x0000020804040210 0x01018e0103008c1d 0xb0040638040c0230

def z32 : W := mkw 0x0004041a00090141 0x4000101068002405 0x003c003e001f03c2 0x0c00f000f8007c0f

def z33 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xfe027000fc007020 0x43f809c003f001c0

def z34 : W := mkw 0xad07de1bb709ed4f 0x42b41f786edc27b5 0xff3ffe3fff1fffff 0xfffcfff8fffc7fff

def z35 : W := mkw 0xad03ca01b300c40a 0x02b40f2806cc0310 0xff03fe01e300000d 0xe3fc0ff8078c0000

def z36 : W := mkw 0x025030840c4428a4 0x800940c2103110a2 0x861070061c040cc9 0x121841c018701033

def z37 : W := mkw 0x5af3b1ed6cfcfbad 0x816bcec7b5b3f3ee 0xfef3f1fffcfcffff 0xfffbcfc7fff3f3ff

def z38 : W := mkw 0x0000100004002804 0x00000040001000a0 0x860270001c00fc3d 0x721809c0007003f0

def z39 : W := mkw 0xaf53fac5bf64feae 0x82bd4feb16fd93fa 0xffd3ffc7ffe4ffff 0xffff4fff1fff93ff

def z40 : W := mkw 0x0803012000000000 0x00200c0480000000 0x000381f800000004 0x08000e07e0000000

def z41 : W := mkw 0x18a381212000c008 0x00628e0484800300 0x78e381f9e000f036 0xe9e38e07e78003c0

def z42 : W := mkw 0x2500000092000000 0x0094000002480000 0x7f000001ff000031 0xf1fc000007fc0000

def z43 : W := mkw 0x080380012000c008 0x00200e0004800300 0x000380000000f004 0x00000e00000003c0

def z44 : W := mkw 0x7fff877bfbffd779 0x45fffe1defefff5d 0x7fff8fffffffffff 0xfdfffe3fffffffff

def z45 : W := mkw 0xad03ca01b300c40a 0x02b40f2806cc0310 0x79018e01e3000000 0x81e40638078c0000

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x013c0001031f0013 0xb404f000040c7c00

def z47 : W := mkw 0x3ffb69a400000000 0x08ffeda690000000 0xbec271c000000000 0x42fb09c700000000

def z48 : W := mkw 0x0000820101008408 0x0000020804040210 0x00018e0000008c0c 0x0000063800000230

def z49 : W := mkw 0x0250b2c50d64beac 0x800942cb143592fa 0x87d3ffc71fe4ffff 0xfe1f4fff1c7f93ff

def z50 : W := mkw 0x50a0804960b8d309 0x014282012582e34c 0x78e00001e0f8f332 0xe5e380000783e3cc

def z51 : W := mkw 0x8807ffb72500ec0e 0x0a201ffedc9403b0 0x8003fffe0000fc0c 0x0a000ffff80003f0

def z52 : W := mkw 0x12fc35f60c643aa4 0x884bf0d7d83190ea 0x86fe71fe1ce4ffff 0x7e1bf9c7f87393ff

def z53 : W := mkw 0x3fff6db648d60030 0x0cfffdb6d9235800 0xbffffffe00ff000f 0xeefffffff803fc00

def z54 : W := mkw 0x0000820101008408 0x0000020804040210 0x0000000103008c10 0x10000000040c0230

def z55 : W := mkw 0x00000000d2920010 0x04000000034a4800 0x40000001e31b0000 0x01000000078c6c00

def z56 : W := mkw 0x58a38169fafed339 0x05628e05a7ebfb4c 0x78e381f9fffff336 0xfde38e07e7ffffcc

def z57 : W := mkw 0xc0009249f7b8ff0f 0x0300024927dee3fc 0x40000001fff8ff30 0x1500000007ffe3fc

def z58 : W := mkw 0xbffbda01ffd6ec3e 0x06ffef6807ff5bb0 0xfffffe01fffffc3f 0xf7fffff807fffff0

def z59 : W := mkw 0x10a8000040920010 0x0442a00001024800 0x002c0000001b0000 0x0000b00000006c00

def z60 : W := mkw 0xad03da41bf64feae 0x82b40f6906fd93fa 0xff03fe01ffe4fffd 0xf7fc0ff807ff93ff

def z61 : W := mkw 0x7fffedff60b8d309 0x09ffffb7fd82e34c 0xffffffffe0f8f33f 0xefffffffff83e3cc

def z62 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe00048fdf 0xfefffffff800123f

def z63 : W := mkw 0xad035a00b7006c06 0x02b40d6802dc01b0 0xff027e00ff007c29 0x53fc09f803fc01f0

def z64 : W := mkw 0x3fff7df6def63ab4 0x8cfffdf7db7bd8ea 0xffffffffffffffff 0xffffffffffffffff

def z65 : W := mkw 0x50a0012840980101 0x01428004a1026004 0x0020003800180000 0x00008000e0006000

def z66 : W := mkw 0x0000100004002804 0x00000040001000a0 0x860070001c000c09 0x121801c000700030

def z67 : W := mkw 0x0000800900088109 0x0000020024002204 0x0021803900180000 0x80008600e4006000

def z68 : W := mkw 0x0250000008440020 0x0009400000211000 0x06d000061ce48fff 0x7c1b40001873923f

def z69 : W := mkw 0x025434d60c643aa4 0x800950d3583190ea 0x87fffffe1ce4ffff 0xfe1ffffff87393ff

def z70 : W := mkw 0x3fffefbf01098549 0x48ffffbefc042615 0xbfffffff031f8fdf 0xfefffffffc0c7e3f

def z71 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff007020 0xc3fc0ff807fc01c0

def z72 : W := mkw 0x025436960d452ce4 0xc00950da583514b3 0x871c7e061f070cc9 0x121c71f8187c1c33

def z73 : W := mkw 0xbfffffb7ffd6ec3e 0x0efffffedfff5bb0 0xfffffffffffffc3f 0xfffffffffffffff0

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0x78000001e0000030 0xe1e0000007800000

def z75 : W := mkw 0x58a7877b61b9d749 0x41629e1ded86e75d 0x78e38fffe0f8fffe 0xede38e3fff83e3ff

def z76 : W := mkw 0x00000000dad60030 0x04000000036b5800 0x40000001ffff0030 0x1500000007fffc00

def z77 : W := mkw 0x8807de1b2509ed4f 0x42201f786c9427b5 0x813ffe3f031fffdf 0xbe04fff8fc0c7fff

def z78 : W := mkw 0x50a0016840b81301 0x01428005a102e04c 0x00e001f800f80302 0x0c038007e003e00c

def z79 : W := mkw 0xfda3db69f7b8ff0f 0x03f68f6da7dee3fc 0xffe3fff9fff8ff3f 0xffff8fffe7ffe3fc

def z80 : W := mkw 0x3fff6db69a460030 0x0cfffdb6da691800 0xbffffffe1f07000f 0xfafffffff87c1c00

def z81 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78f381ffe0fcffff 0xfde3ce07ff83f3ff

def z82 : W := mkw 0x0004041200000000 0x0000101048000000 0x013d8e3e00048fdf 0xbc04f638f800123f

def z83 : W := mkw 0x10a0000040900000 0x0042800001024000 0x78e00001e0f80032 0xe5e380000783e000

def z84 : W := mkw 0x0004861b01098549 0x400012186c042615 0x003d8e3e001f8fce 0x0c00f638f8007e3f

def z85 : W := mkw 0x2d03480000000000 0x00b40d2000000000 0xbf03fe000000000d 0xe2fc0ff800000000

def z86 : W := mkw 0xbfffffb7b700ec0e 0x0afffffededc03b0 0xffffffffff00fc3f 0xfbfffffffffc03f0

def z87 : W := mkw 0x2500000092000000 0x0094000002480000 0x79000001e3000000 0x81e40000078c0000

def z88 : W := mkw 0x7dab8129f29ac119 0x05f6ae04a7ca6b04 0x792d8039e31b0000 0x81e4b600e78c6c00

def z89 : W := mkw 0x0250000008440020 0x0009400000211000 0x06d000001ce40033 0x741b400000739000

def z90 : W := mkw 0x3fff7df604203a84 0x88fffdf7d81080ea 0xbffffffe0000ffcf 0xeafffffff80003ff

def z91 : W := mkw 0x0004861b01098549 0x400012186c042615 0x003c003f031f8fd2 0x1c00f000fc0c7e3f

def z92 : W := mkw 0x000092490d6dbfed 0xc00002492435b6ff 0x000000011ffffff0 0x14000000047fffff

def z93 : W := mkw 0x8803da012500ec0e 0x02200f68049403b0 0x8103fe010300fc1d 0xb2040ff8040c03f0

def z94 : W := mkw 0x7fffedff2028d309 0x09ffffb7fc80a34c 0xbffffffe0000f30f 0xeafffffff80003cc

def z95 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c01ce47033 0x761b49c7007391c0

def z96 : W := mkw 0x3fff6db608440020 0x08fffdb6d8211000 0xbffffffe1ce4003f 0xfefffffff8739000

def z97 : W := mkw 0x000010400c643aa4 0x80000041003190ea 0x000000001ce4fff0 0x14000000007393ff

def z98 : W := mkw 0x275c7c960c4428a4 0x889d71f2583110a2 0x871c7e061c040cc9 0x121c71f818701033

def z99 : W := mkw 0x0000800900088109 0x0000020024002204 0x013d8039031f8317 0xbc04f600e40c7e0c

def z100 : W := mkw 0x18a3012000000000 0x00628c0480000000 0x38e381f800000006 0xe8e38e07e0000000

def z101 : W := mkw 0x12f80000dad60030 0x044be000036b5800 0x40fc0001ffff0032 0x1503f00007fffc00

def z102 : W := mkw 0x0000004000201200 0x0000000100008048 0x0000000000e0f330 0x04000000000383cc

def z103 : W := mkw 0x12f8000048d60030 0x044be00001235800 0x00fc000000ff0002 0x0403f0000003fc00

def z104 : W := mkw 0x0004061201010440 0x4000101848040411 0x010c0e0003030000 0x00043038000c0c00

def z105 : W := mkw 0x275c6c9600000000 0x089d71b258000000 0x871c7e0600000009 0x021c71f818000000

def z106 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78c201c0e0e07020 0x41e30807038381c0

def z107 : W := mkw 0x58a381296098c109 0x01628e04a5826304 0x78238039e018f034 0xe1e08e00e78063c0

def z108 : W := mkw 0x25000000dad60030 0x04940000036b5800 0x7f000001ffff0031 0xf5fc000007fffc00

def z109 : W := mkw 0x0a53b0c52c64faac 0x80294ec314b193ea 0xfed3f1c7fce4ffff 0xfffb4fc71ff393ff

def z110 : W := mkw 0x0004861b01098549 0x400012186c042615 0x00018e3e00008fcc 0x08000638f800023f

def z111 : W := mkw 0x0000800100008008 0x0000020004000200 0x0001800100008014 0xa000060004000200

def z112 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e39031f0013 0xb404f638e40c7c00

def z113 : W := mkw 0xfda35960f6b07a06 0x03f68d6583dac1e8 0xfec271c0fce07020 0x43fb09c703f381c0

def z114 : W := mkw 0x37f830c4def63ab4 0x84dfe0c3137bd8ea 0xfffe71c7ffffffff 0xfffff9c71fffffff

def z115 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ec00000fce00020 0x41fb000003f38000

def z116 : W := mkw 0xad07de13b700ec0e 0x02b41f784edc03b0 0xff3ffe3fff00fc3f 0xfbfcfff8fffc03f0

def z117 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff01fe01ff000c09 0x93fc07f807fc0030

def z118 : W := mkw 0xad03d801b600e80e 0x02b40f6006d803a0 0xfe03f001fc00f034 0xe3f80fc007f003c0

def z119 : W := mkw 0x8803da012500ec0e 0x02200f68049403b0 0x8003fe000000fc0c 0x02000ff8000003f0

def z120 : W := mkw 0x12fc25be00090141 0x484bf096f8002405 0x00fc01fe001f03c2 0x0c03f007f8007c0f

def z121 : W := mkw 0x0000000800080101 0x0000000020002004 0x0020003800180302 0x0c008000e000600c

def z122 : W := mkw 0x0000100004002804 0x00000040001000a0 0x800270000000fc0c 0x020009c0000003f0

def z123 : W := mkw 0x58a381296098c109 0x01628e04a5826304 0x78e381f9e0180006 0xe9e38e07e7806000

def z124 : W := mkw 0x2d03ca0101008408 0x00b40f2804040210 0xbf03fe0103008c1d 0xf2fc0ff8040c0230

def z125 : W := mkw 0xa5045e1297012c46 0x429411784a5c04b1 0x871c7e061f070cc9 0x121c71f8187c1c33

def z126 : W := mkw 0xad03da41b720fe0e 0x02b40f6906dc83f8 0xffc3ffc1ffe0ff3f 0xffff0fff07ff83fc

def z127 : W := mkw 0x275800009a460030 0x049d600002691800 0x071c00001f070001 0x101c7000007c1c00

def z128 : W := mkw 0x480381692028d309 0x01200e05a480a34c 0x000381f80000f304 0x08000e07e00003cc

def z129 : W := mkw 0x4000804960b8d309 0x010002012582e34c 0x40000001e0f8f330 0x050000000783e3cc

def z130 : W := mkw 0x000030c404203a84 0x800000c3101080ea 0x800271c000007000 0x020009c7000001c0

def z131 : W := mkw 0x80009201b700ec0e 0x0200024806dc03b0 0xc6027001ff00fc3d 0x731809c007fc03f0

def z132 : W := mkw 0x0000004000201200 0x0000000100008048 0x00c201c000e0f336 0x6c030807000383cc

def z133 : W := mkw 0x58a381296098c109 0x01628e04a5826304 0x78218039e0180000 0x81e08600e7806000

def z134 : W := mkw 0x7ffb8169fafed339 0x05ffee05a7ebfb4c 0x7fff81f9fffff337 0xfdfffe07e7ffffcc

def z135 : W := mkw 0x7dafcd3b6098c109 0x09f6bf34ed826304 0x792d8e39e0180000 0x81e4b638e7806000

def z136 : W := mkw 0xad07ce1bb309c54b 0x42b41f386ecc2715 0x792d8e39e31b0000 0x81e4b638e78c6c00

def z137 : W := mkw 0xad03da012500ec0e 0x02b40f68049403b0 0xbf03fe000000fc0d 0xe2fc0ff8000003f0

def z138 : W := mkw 0x0004041200000000 0x0000101048000000 0x00018e3e0000000c 0x08000638f8000000

def z139 : W := mkw 0xa5005a0097002c06 0x02940168025c00b0 0x87007e001f000c09 0x121c01f8007c0030

def z140 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c61ce0ffec 0x4a1b09c7187383ff

def z141 : W := mkw 0x7fffefff61b9d749 0x49ffffbffd86e75d 0xffffffffe3ffffff 0xffffffffff8fffff

def z142 : W := mkw 0x80009201b700ec0e 0x0200024806dc03b0 0x40000001ff00fc30 0x1100000007fc03f0

def z143 : W := mkw 0x5af331e46cf47aa4 0x816bccc791b3d1ea 0xfec271c0fce07020 0x43fb09c703f381c0

def z144 : W := mkw 0x3fff6db640900000 0x08fffdb6d9024000 0xffffffffe0f8003f 0xefffffffff83e000

def z145 : W := mkw 0xa75c7e9697002c06 0x0a9d71fa5a5c00b0 0x871c7e061f000c09 0x121c71f8187c0030

def z146 : W := mkw 0x50a0816960b8d309 0x01428205a582e34c 0x40e001f9e0f8f332 0x0d038007e783e3cc

def z147 : W := mkw 0x3da3492000000000 0x00f68d2480000000 0xbfe3fff80000000f 0xeaff8fffe0000000

def z148 : W := mkw 0x77f80168dafe1331 0x05dfe005a36bf84c 0x7ffc01f9ffff0333 0xfdfff007e7fffc0c

def z149 : W := mkw 0x025030840c4428a4 0x800940c2103110a2 0x86d070061ce40cfb 0x761b41c018739033

def z150 : W := mkw 0x7fff6dfe40b81301 0x09fffdb7f902e04c 0xbffffffe00f8030f 0xeefffffff803e00c

def z151 : W := mkw 0x0004841b00098149 0x400012106c002605 0x003d803f001f83d6 0xac00f600fc007e0f

def z152 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0007ffff8fff 0xfdfff0001ffffe3f

def z153 : W := mkw 0x3ffb79e40c643aa4 0x88ffede7903190ea 0xbec271c01ce07020 0x42fb09c7007381c0

def z154 : W := mkw 0x12fc25b600000000 0x084bf096d8000000 0x00fc01fe00000002 0x0803f007f8000000

def z155 : W := mkw 0xaf53fac5bf64feae 0x82bd4feb16fd93fa 0xffc3ffc1ffe0fc3d 0xf3ff0fff07ff83f0

def z156 : W := mkw 0x0004041200000000 0x0000101048000000 0x011c0e0600000009 0x0004703818000000

def z157 : W := mkw 0x0250208408440020 0x0009408210211000 0x86d271c61ce4003f 0x7e1b49c718739000

def z158 : W := mkw 0xed03db69b728ff0f 0x03b40f6da6dca3fc 0xff03fff9ff00ff3d 0xfbfc0fffe7fc03fc

def z159 : W := mkw 0x37f81040def63ab4 0x84dfe041037bd8ea 0x7ffc0001fffffff3 0xf5fff00007ffffff

def z160 : W := mkw 0x3ffb8001fad6c038 0x04ffee0007eb5b00 0x7fff8001fffff037 0xf5fffe0007ffffc0

def z161 : W := mkw 0x0000020001010440 0x4000000800040411 0x0000000003070cc0 0x10000000000c1c33

def z162 : W := mkw 0x025020c4086412a0 0x800940831021904a 0x06d001c61ce403f3 0x7c1b40071873900f

def z163 : W := mkw 0x0254861b094d8569 0x400952186c253615 0x07fd8e3f1fff8fff 0xfc1ff638fc7ffe3f

def z164 : W := mkw 0x3fff6db692000000 0x08fffdb6da480000 0xffffffffff00003f 0xfbfffffffffc0000

def z165 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xff027001ff007031 0xf3fc09c007fc01c0

def z166 : W := mkw 0x50a4057a40b91341 0x41429015e902e44d 0x00fc01fe00ff03c2 0x0c03f007f803fc0f

def z167 : W := mkw 0x3daf6db600000000 0x08f6bdb6d8000000 0xb92ffffe0000000c 0x8ae4bffff8000000

def z168 : W := mkw 0x0000308404002884 0x800000c2101000a2 0x8000700600000cc8 0x020001c018000033

def z169 : W := mkw 0x0004041a00090141 0x4000101068002405 0x003c003e001f8fdf 0x3c00f000f8007e3f

def z170 : W := mkw 0x0000820901098549 0x4000020824042615 0x01018e01031f8fdd 0xb4040638040c7e3f

def z171 : W := mkw 0x4000004840b81301 0x010000012102e04c 0x0000000000f80300 0x040000000003e00c

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000001031f0010 0x14000000040c7c00

def z173 : W := mkw 0x3ffb69a400000000 0x08ffeda690000000 0xbfc3ffc00000000d 0xe2ff0fff00000000

def z174 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xff03fe00fc00702d 0xe3fc0ff803f001c0

def z175 : W := mkw 0x0004061201010440 0x4000101848040411 0x011c0e0603070cc9 0x10047038180c1c33

def z176 : W := mkw 0x3fffefb701008408 0x08ffffbedc040210 0xbfffffff03008c1f 0xfafffffffc0c0230

def z177 : W := mkw 0x3fff7df60c643aa4 0x88fffdf7d83190ea 0xbffffffe1ce4ffff 0xfefffffff87393ff

def z178 : W := mkw 0x80008201b300c40a 0x0200020806cc0310 0x40000001e3000000 0x01000000078c0000

def z179 : W := mkw 0x0000000092000000 0x0000000002480000 0x40000001ff000030 0x1100000007fc0000

def z180 : W := mkw 0x0004861301008408 0x000012184c040210 0x013d8e3f03008c1f 0xb804f638fc0c0230

def z181 : W := mkw 0x025030840c4428a4 0x800940c2103110a2 0x861070061c048fdf 0x3e1841c01870123f

def z182 : W := mkw 0x12f820c448f612b0 0x844be0831123d84a 0x00fc01c600ff03c2 0x0c03f0071803fc0f

def z183 : W := mkw 0x35a80000d2920010 0x04d6a000034a4800 0x79ec0001e3fb0032 0xe5e7b000078fec00

def z184 : W := mkw 0x025020c4086412a0 0x800940831021904a 0x00d001c600e403c2 0x0c0340071803900f

def z185 : W := mkw 0x2500000092000000 0x0094000002480000 0x7f3c0001ff1f0033 0xf5fcf00007fc7c00

def z186 : W := mkw 0x00046c9600000000 0x080011b258000000 0x80007e0600000008 0x020001f818000000

def z187 : W := mkw 0xbdabca01f392c41a 0x06f6af2807ce4b10 0x792d8e01e31b0000 0x81e4b638078c6c00

def z188 : W := mkw 0x2d074c1200000000 0x00b41d3048000000 0xbf3ffe3e0000000f 0xeafcfff8f8000000

def z189 : W := mkw 0x5af3816968fcd329 0x016bce05a5a3f34c 0x7ef381f9fcfcf337 0xfdfbce07e7f3f3cc

def z190 : W := mkw 0x4807edff2028d309 0x09201fb7fc80a34c 0x8003fffe0000f30c 0x0a000ffff80003cc

def z191 : W := mkw 0x2f53688400000000 0x00bd4da210000000 0xbfd3ffc60000000f 0xeaff4fff18000000

def z192 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xfe03fe00fc00fc2c 0x43f80ff803f003f0

def z193 : W := mkw 0x35a80000d2920010 0x04d6a000034a4800 0x792c0001e31b0000 0x81e4b000078c6c00

def z194 : W := mkw 0x12f8000000000000 0x004be00000000000 0x00fc000000000002 0x0003f00000000000

def z195 : W := mkw 0x080369a400000000 0x08200da690000000 0x800271c000000000 0x020009c700000000

def z196 : W := mkw 0x275800009a460030 0x049d600002691800 0x7f1c0001ff070031 0xf1fc700007fc1c00

def z197 : W := mkw 0x37fc861bdbdf8579 0x44dff2186f6f7e15 0x7ffd8e3fffff8fff 0xfdfff638fffffe3f

def z198 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000600040cc9 0x1000400018001033

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x013c000000000003 0xa004f00000000000

def z200 : W := mkw 0x4803016020205200 0x01200c0580808148 0x000201c000007000 0x00000807000001c0

def z201 : W := mkw 0x000425b600000000 0x08001096d8000000 0x000001fe00000000 0x08000007f8000000

def z202 : W := mkw 0x025020c4086412a0 0x800940831021904a 0x86d271c600e403cf 0x6e1b49c71803900f

def z203 : W := mkw 0x025010400c643aa4 0x80094041003190ea 0x06d000001ce4fff3 0x741b4000007393ff

def z204 : W := mkw 0x000030c404203a84 0x800000c3101080ea 0x80c271c600e0fffe 0x6e0309c7180383ff

def z205 : W := mkw 0x4803804960b8d309 0x01200e012582e34c 0x78038001e0f8f334 0xe5e00e000783e3cc

def z206 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbec3fffe0000000c 0x4afb0ffff8000000

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x013c0007031f8fdf 0xbc04f0001c0c7e3f

def z208 : W := mkw 0x3dafcf3b01098549 0x48f6bf3cec042615 0x393d8e3f031f8fdf 0xbce4f638fc0c7e3f

def z209 : W := mkw 0x18a3012040900000 0x00628c0481024000 0x78e381f9e0f80036 0xede38e07e783e000

def z210 : W := mkw 0x000080012000c008 0x0000020004800300 0x40000001e000f030 0x01000000078003c0

def z211 : W := mkw 0x0000820901098549 0x4000020824042615 0x00100007031f8fdf 0x3c0040001c0c7e3f

def z212 : W := mkw 0x3daf4d32d2920010 0x0cf6bd34cb4a4800 0x792d8e39e31b0000 0x81e4b638e78c6c00

def z213 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78e381f8e0e07026 0xe9e38e07e38381c0

def z214 : W := mkw 0x0250208400000000 0x0009408210000000 0x8610700600000009 0x021841c018000000

def z215 : W := mkw 0x37fc861b01098549 0x40dff2186c042615 0x3ffd8e3f031f8fdf 0xfcfff638fc0c7e3f

def z216 : W := mkw 0x58a381692028d309 0x01628e05a480a34c 0x38e381f80000f306 0xe8e38e07e00003cc

def z217 : W := mkw 0x7ffb0160faf65230 0x05ffec0583ebd948 0x7ffe01c1ffff7033 0xf5fff80707fffdc0

def z218 : W := mkw 0x35ac861bd39b8559 0x44d6b2186f4e6e15 0x793d8e3fe31f8fdf 0xbde4f638ff8c7e3f

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x860270000000000d 0x621809c000000000

def z220 : W := mkw 0x0004865b01299749 0x400012196c04a65d 0x01ff8fff03ffffff 0xfc07fe3ffc0fffff

def z221 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0x39fd8ffe00000002 0x88e7f63ff8000000

def z222 : W := mkw 0x3fff6db6d2920010 0x0cfffdb6db4a4800 0xffffffffe31b000f 0xebffffffff8c6c00

def z223 : W := mkw 0x025030c404203a84 0x800940c3101080ea 0x86d271c60000ffcf 0x6a1b49c7180003ff

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x00100006000403c2 0x0c0040001800100f

def z225 : W := mkw 0x0254b6df0d6dbfed 0xc00952db7c35b6ff 0x87ffffff1fffffff 0xfe1ffffffc7fffff

def z226 : W := mkw 0xaf57fedfbf6dffef 0xc2bd5ffb7efdb7ff 0xffffffffffffffff 0xffffffffffffffff

def z227 : W := mkw 0x2500100096002804 0x00940040025800a0 0xff027001ff00fc3d 0xf3fc09c007fc03f0

def z228 : W := mkw 0x0004861b01098549 0x400012186c042615 0x00018e3f031f8fdc 0x1c000638fc0c7e3f

def z229 : W := mkw 0x4807877b2129d749 0x41201e1dec84a75d 0x013f8fff031fffdf 0xbc04fe3ffc0c7fff

def z230 : W := mkw 0x2d07ce1b01098549 0x40b41f386c042615 0xbf3ffe3f031f8fdf 0xfefcfff8fc0c7e3f

def z231 : W := mkw 0x2758688400000000 0x089d61a210000000 0x8600700000000000 0x021801c000000000

def z232 : W := mkw 0x12fc25b600000000 0x084bf096d8000000 0x01fd8ffe0000000f 0xa807f63ff8000000

def z233 : W := mkw 0x0250b2cd0d6dbfed 0xc00942cb3435b6ff 0x86d271c71fffffff 0x7e1b49c71c7fffff

def z234 : W := mkw 0xad03da09b708ed0f 0x02b40f6826dc23b4 0xff23fe39ff18ff3f 0xfffc8ff8e7fc63fc

def z235 : W := mkw 0x400090496cfcfbad 0x8100024125b3f3ee 0x40000001fcfcfff0 0x1500000007f3f3ff

def z236 : W := mkw 0x10a0800940988109 0x0042820025026204 0x78e18039e0f88336 0xede38600e783e20c

def z237 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbefe71fe00000002 0x4afbf9c7f8000000

def z238 : W := mkw 0xbffb5800fed66836 0x06ffed6003fb59a0 0xfffe7001ffff7033 0xf7fff9c007fffdc0

def z239 : W := mkw 0xa5005a0097002c06 0x02940168025c00b0 0xff007e01ff000c39 0xf3fc01f807fc0030

def z240 : W := mkw 0xfda3cb29f398c50b 0x03f68f2ca7ce6314 0x79218e39e3180000 0x81e48638e78c6000

def z241 : W := mkw 0x80001000b6006806 0x0200004002d801a0 0x40000000fc007020 0x0100000003f001c0

def z242 : W := mkw 0x000010000c4428a4 0x80000040003110a2 0x000000001c040cc0 0x1000000000701033

def z243 : W := mkw 0xaf5bda01bf46ec3e 0x06bd6f6806fd1bb0 0xff1ffe01ff07fc3d 0xf3fc7ff807fc1ff0

def z244 : W := mkw 0x18a380016090c008 0x00628e0005824300 0x78e38001e0f8f036 0xe5e38e000783e3c0

def z245 : W := mkw 0x3daf4d3200000000 0x08f6bd34c8000000 0x393d8e3e0000000f 0xa8e4f638f8000000

def z246 : W := mkw 0x37f830c4def63ab4 0x84dfe0c3137bd8ea 0xfed271c6fce4ffff 0x7ffb49c71bf393ff

def z247 : W := mkw 0x275c6e9601010440 0x489d71ba58040411 0x871c7e0603070cc9 0x121c71f8180c1c33

def z248 : W := mkw 0x0004861b01098549 0x400012186c042615 0x011d8e3e03078fcd 0x18047638f80c1e3f

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0000000e00032 0x6403000000038000

def z250 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xf903fe01e300fc0c 0x83e40ff8078c03f0

def z251 : W := mkw 0x0250208400000000 0x0009408210000000 0x86c271c000000000 0x421b09c700000000

def z252 : W := mkw 0x37fc041200000000 0x00dff01048000000 0x3ffd8e3e0000000f 0xe8fff638f8000000

def z253 : W := mkw 0x10a4861b41998549 0x404292186d066615 0x79fd8e3fe3ff8fff 0xfde7f638ff8ffe3f

def z254 : W := mkw 0x88039201b700ec0e 0x02200e4806dc03b0 0x78038001ff00fc34 0xf1e00e0007fc03f0

def z255 : W := mkw 0x275800009a460030 0x049d600002691800 0x060000001c000000 0x0018000000700000

def z256 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c01ce0f336 0x6e1b09c7007383cc

def z257 : W := mkw 0x52f8016848fe1331 0x054be005a123f84c 0x00fc01f800ff0302 0x0c03f007e003fc0c

def z258 : W := mkw 0xed03da49f7b8ff0f 0x03b40f6927dee3fc 0xff03fe01fff8ff3d 0xf7fc0ff807ffe3fc

def z259 : W := mkw 0x0250000008440020 0x0009400000211000 0x07fc00011fff0033 0xf41ff000047ffc00

def z260 : W := mkw 0x0004861b01098549 0x400012186c042615 0x012d8e39031f8fd0 0x9404b638e40c7e3f

def z261 : W := mkw 0x00000000dad60030 0x04000000036b5800 0x413c0001ffff0033 0xb504f00007fffc00

def z262 : W := mkw 0x0004041200000000 0x0000101048000000 0x013d8e3f031f001f 0xbc04f638fc0c7c00

def z263 : W := mkw 0x37f88209dbdf8579 0x44dfe208276f7e15 0x7ffc0001ffff8ff3 0xf5fff00007fffe3f

def z264 : W := mkw 0x800092012500ec0e 0x02000248049403b0 0x000000000000fc00 0x00000000000003f0

def z265 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0x8703fe001f00fc0d 0x121c0ff8007c03f0

def z266 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff13fe07ff04ffff 0xfffc4ff81ffc13ff

def z267 : W := mkw 0x0004041200000000 0x0000101048000000 0x003c003e00000002 0x0800f000f8000000

def z268 : W := mkw 0x7da38169f2b8d309 0x01f68e05a7cae34c 0x7fe381f9fff8f337 0xfdff8e07e7ffe3cc

def z269 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c01ce4fff0 0x561b09c7007393ff

def z270 : W := mkw 0x8803da012500ec0e 0x02200f68049403b0 0x8603fe001c00fc3d 0x72180ff8007003f0

def z271 : W := mkw 0xa7507a849f442ca6 0x829d41ea127d10b2 0x87107e061f040cc9 0x121c41f8187c1033

def z272 : W := mkw 0x0803000000000000 0x00200c0000000000 0x3803800000000004 0xe0e00e0000000000

def z273 : W := mkw 0x12fca7bf01098549 0x484bf29efc042615 0x01fd8fff031f8fdf 0xbc07f63ffc0c7e3f

def z274 : W := mkw 0x3ffb79e40c643aa4 0x88ffede7903190ea 0xbed271c61ce4ffff 0x7efb49c7187393ff

def z275 : W := mkw 0x2f5f6db600000000 0x08bd7db6d8000000 0x871ffffe0000000d 0x0a1c7ffff8000000

def z276 : W := mkw 0x0004061201010440 0x4000101848040411 0x013d8e3e03070ccf 0xb804f638f80c1c33

def z277 : W := mkw 0xbffbfba5b700ec0e 0x0affefee96dc03b0 0xffc3ffc1ff00fc3d 0xf3ff0fff07fc03f0

def z278 : W := mkw 0x3ffb69a400000000 0x08ffeda690000000 0xbee3f1f800000006 0xeafb8fc7e0000000

def z279 : W := mkw 0x480381292008c109 0x01200e04a4802304 0x0001803800000000 0x00000600e0000000

def z280 : W := mkw 0x0000100004002804 0x00000040001000a0 0x861270061c04ffff 0x7e1849c0187013ff

def z281 : W := mkw 0x0000004000201200 0x0000000100008048 0x000201c00000f304 0x08000807000003cc

def z282 : W := mkw 0x0000820901098549 0x4000020824042615 0x00218039031f8fd6 0xbc008600e40c7e3f

def z283 : W := mkw 0x000010400c643aa4 0x80000041003190ea 0x00c201c01ce4fff6 0x7c030807007393ff

def z284 : W := mkw 0x58a3836961b9d749 0x41628e0da586e75d 0x78e381f9e3fffff6 0xfde38e07e78fffff

def z285 : W := mkw 0xbffbfac5fff6febe 0x86ffefeb17ffdbfa 0xffffffc7ffffffff 0xffffffff1fffffff

def z286 : W := mkw 0xa5009201b700ec0e 0x0294024806dc03b0 0x7f000001ff00fc31 0xf1fc000007fc03f0

def z287 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x79ff81f9e3fff337 0xfde7fe07e78fffcc

def z288 : W := mkw 0x37fc0412dad60030 0x04dff0104b6b5800 0x7ffd8e3fffff003f 0xfdfff638fffffc00

def z289 : W := mkw 0x18a76db600000000 0x08629db6d8000000 0xb8e3fffe0000000e 0xeae38ffff8000000

def z290 : W := mkw 0x4000004060b05200 0x010000010182c148 0x40000000e0e07020 0x01000000038381c0

def z291 : W := mkw 0x8803fac52520fe8e 0x82200feb149483fa 0x8003ffc60000ffcc 0x0a000fff180003ff

def z292 : W := mkw 0x3ffb012000000000 0x00ffec0480000000 0x3fff81f800000007 0xe8fffe07e0000000

def z293 : W := mkw 0x3daf4d3200000000 0x08f6bd34c8000000 0x39ef8ff800000006 0xe8e7be3fe0000000

def z294 : W := mkw 0x1aff6db600000000 0x086bfdb6d8000000 0x80fffffe0000000e 0x0a03fffff8000000

def z295 : W := mkw 0xbffb5800fed66836 0x06ffed6003fb59a0 0xfec27000fce07020 0x43fb09c003f381c0

def z296 : W := mkw 0x2f5f6c9600000000 0x08bd7db258000000 0xbf1ffe060000000d 0xe2fc7ff818000000

def z297 : W := mkw 0x0a576db600000000 0x08295db6d8000000 0x86d3fffe0000000f 0x6a1b4ffff8000000

def z298 : W := mkw 0x0803000020004000 0x00200c0000800100 0x78020000e0007020 0x41e00800038001c0

def z299 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f87020 0xc1e38e07e783e1c0

def z300 : W := mkw 0x275800009a460030 0x049d600002691800 0x073c00011f1f0013 0xb41cf000047c7c00

def z301 : W := mkw 0x37f88201dbd68438 0x04dfe208076f5a10 0x7ffd8e01ffff8c3f 0xf5fff63807fffe30

def z302 : W := mkw 0x58a3b1ed64b8fb8d 0x81628ec7b592e3ee 0xf8e3f1ffe0f8fffe 0xefe38fc7ff83e3ff

def z303 : W := mkw 0x7ffffdff6cfcfbad 0x89fffff7fdb3f3ee 0xfffffffffcfcffff 0xfffffffffff3f3ff

def z304 : W := mkw 0x2500000092000000 0x0094000002480000 0x070000001f000001 0x101c0000007c0000

def z305 : W := mkw 0x12f0000048d40020 0x004bc00001235000 0x7ef00001fcfc0033 0xf5fbc00007f3f000

def z306 : W := mkw 0x2d03480092000000 0x00b40d2002480000 0xff03fe01ff00003d 0xf3fc0ff807fc0000

def z307 : W := mkw 0x12f830c44cf63ab4 0x844be0c31133d8ea 0x86fe71c61cffffff 0x7e1bf9c71873ffff

def z308 : W := mkw 0x8803ca012100c40a 0x02200f2804840310 0x00018e0000000000 0x0000063800000000

def z309 : W := mkw 0x4004865b61b9d749 0x410012196d86e75d 0x413d8e3fe3ffffff 0xbd04f638ff8fffff

def z310 : W := mkw 0x0004b6df0529bfcd 0xc00012db7c14a6ff 0x813fffff031fffdf 0xbe04fffffc0c7fff

def z311 : W := mkw 0x0254b69f0d4daded 0xc00952da7c3536b7 0x873dfe3f1f1f8fdf 0xbe1cf7f8fc7c7e3f

def z312 : W := mkw 0x0000820901098549 0x4000020824042615 0x0000000000008fc0 0x000000000000023f

def z313 : W := mkw 0x50a0016840b81301 0x01428005a102e04c 0x78e001f9e0f80332 0xede38007e783e00c

def z314 : W := mkw 0x5af7b7ff6dfdffed 0xc16bdedffdb7f7ff 0xffffffffffffffff 0xffffffffffffffff

def z315 : W := mkw 0x025424de086d13e1 0xc00950937821b44f 0x00fc01fe00ff03c2 0x0c03f007f803fc0f

def z316 : W := mkw 0x37f88009dade8139 0x04dfe200276b7a04 0x7ffd8039ffff8337 0xfdfff600e7fffe0c

def z317 : W := mkw 0x080380012000c008 0x00200e0004800300 0x78038001e000f034 0xe1e00e00078003c0

def z318 : W := mkw 0x0004061201010440 0x4000101848040411 0x00000e0600000cc8 0x0000003818000033

def z319 : W := mkw 0x000030c404203a84 0x800000c3101080ea 0x800271c60000ffcc 0x0a0009c7180003ff

def z320 : W := mkw 0x3ffb0120dad60030 0x04ffec04836b5800 0x7fff81f9ffff0037 0xfdfffe07e7fffc00

def z321 : W := mkw 0x7ffb8169fafed339 0x05ffee05a7ebfb4c 0x7ee381f9fcf8f336 0xedfb8e07e7f3e3cc

def z322 : W := mkw 0x2500000092000000 0x0094000002480000 0x7e000000fc000020 0x41f8000003f00000

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x01018e000000000d 0xa004063800000000

def z324 : W := mkw 0x3fff6df6086412a0 0x88fffdb7d821904a 0xbffffffe00e403cf 0xeefffffff803900f

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000103000011 0xb0040000040c0000

def z326 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff3ffe01ff1ffc3f 0xf7fcfff807fc7ff0

def z327 : W := mkw 0x3fff4d3200000000 0x08fffd34c8000000 0x3ffd8e3800000003 0xe0fff638e0000000

def z328 : W := mkw 0x275030c49e643aa4 0x809d40c3127990ea 0xffd271c7ffe4ffff 0xffff49c71fff93ff

def z329 : W := mkw 0xaf5378c4be647aa6 0x82bd4de312f991ea 0xfed271c6fce4ffff 0x7ffb49c71bf393ff

def z330 : W := mkw 0x000000009a460030 0x0400000002691800 0x000000001f070000 0x10000000007c1c00

def z331 : W := mkw 0xbfffffbfb709ed4f 0x4afffffefedc27b5 0xffffffffff1fffff 0xfffffffffffc7fff

def z332 : W := mkw 0x250c4c1200000000 0x0894313048000000 0x010c0e0000000000 0x0004303800000000

def z333 : W := mkw 0x0004061201010440 0x4000101848040411 0x011c0e0603078fdf 0x3c047038180c1e3f

def z334 : W := mkw 0x37f8000048d60030 0x04dfe00001235800 0x3ffc000000ff0003 0xe4fff0000003fc00

def z335 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfeffff800000000 0xc2ffbfffe0000000

def z336 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7f3c0001ff1f0001 0x91fcf00007fc7c00

def z337 : W := mkw 0xaf53fa85bf44ecae 0x82bd4fea16fd13b2 0xff13fe07ff04fcfd 0xf3fc4ff81ffc13f3

def z338 : W := mkw 0xbdafcf33b300c40a 0x0af6bf3ccecc0310 0x792d8e39e3000000 0x81e4b638e78c0000

def z339 : W := mkw 0x8250b2c5bf64feae 0x820942cb16fd93fa 0xc6d271c7ffe4ffff 0x7f1b49c71fff93ff

def z340 : W := mkw 0x1aff25b600000000 0x086bfc96d8000000 0x38ff81fe00000006 0xe8e3fe07f8000000

def z341 : W := mkw 0x480381692028d309 0x01200e05a480a34c 0x002381f90018f316 0xac008e07e40063cc

def z342 : W := mkw 0xad07de13b701ec4e 0x42b41f784edc07b1 0xff1ffe07ff07fcfd 0xf3fc7ff81ffc1ff3

def z343 : W := mkw 0x080380412020d208 0x00200e0104808348 0x78c381c1e0e0f336 0xede30e07078383cc

def z344 : W := mkw 0x5afb816968fed339 0x056bee05a5a3fb4c 0x78ff81f9e0fff336 0xede3fe07e783ffcc

def z345 : W := mkw 0x0000800900088109 0x0000020024002204 0x0000000100188310 0x040000000400620c

def z346 : W := mkw 0x37f820c4daf612b0 0x84dfe083136bd84a 0x7ffc01c7ffff03f3 0xfdfff0071ffffc0f

def z347 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x87fe71c71fffffff 0xfe1ff9c71c7fffff

def z348 : W := mkw 0x0250208400000000 0x0009408210000000 0x86d271c600048fdf 0x7e1b49c71800123f

def z349 : W := mkw 0x025030840c4428a4 0x800940c2103110a2 0x86d271c61c040ccf 0x7a1b49c718701033

def z350 : W := mkw 0x0004041a00090141 0x4000101068002405 0x013d8e3e001f03cf 0xac04f638f8007c0f

def z351 : W := mkw 0x000030c404203a84 0x800000c3101080ea 0x801271c60004ffdf 0x3e0049c7180013ff

def z352 : W := mkw 0x12fc861b49df8579 0x444bf2186d277e15 0x01fd8e3f03ff8fdf 0xbc07f638fc0ffe3f

def z353 : W := mkw 0x27580000dad60030 0x049d6000036b5800 0x471c0001ffff0031 0x151c700007fffc00

def z354 : W := mkw 0x025436d60d653ee4 0xc00950db583594fb 0x87de7fc61fe7ffff 0x7e1f79ff187f9fff

def z355 : W := mkw 0x10a0000040900000 0x0042800001024000 0x78200001e0180000 0x81e0800007806000

def z356 : W := mkw 0xbffbda01b700ec0e 0x02ffef6806dc03b0 0xfffffe01ff00fc3f 0xf3fffff807fc03f0

def z357 : W := mkw 0x0004041a00090141 0x4000101068002405 0x013c003f031f03d3 0xbc04f000fc0c7c0f

def z358 : W := mkw 0x12fc25b648d60030 0x0c4bf096d9235800 0x00fc01fe00ff0002 0x0c03f007f803fc00

def z359 : W := mkw 0x52fc25fe40b81301 0x094bf097f902e04c 0x00fc01fe00f80302 0x0c03f007f803e00c

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000060000000f 0x2800400018000000

def z361 : W := mkw 0x480381692028d309 0x01200e05a480a34c 0x00c381f800e0f336 0x6c030e07e00383cc

def z362 : W := mkw 0x3fff4d32dad60030 0x0cfffd34cb6b5800 0x7ffd8e39ffff0033 0xf5fff638e7fffc00

def z363 : W := mkw 0x50a0016840b81301 0x01428005a102e04c 0x00e201f800f8f336 0x6c038807e003e3cc

def z364 : W := mkw 0x08074d3200000000 0x08201d34c8000000 0x00018e3800000000 0x00000638e0000000

def z365 : W := mkw 0xa5005a0097002c06 0x02940168025c00b0 0x87027e001f00fc3d 0x721c09f8007c03f0

def z366 : W := mkw 0x8803da01b700ec0e 0x02200f6806dc03b0 0xc003fe01ff00fc3c 0x13000ff807fc03f0

def z367 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7fec0001fffb0020 0xc1ffb00007ffec00

def z368 : W := mkw 0x0250208400000000 0x0009408210000000 0x00d001c600000002 0x0803400718000000

def z369 : W := mkw 0x400080096098c109 0x0100020025826304 0x40000001e0180000 0x0100000007806000

def z370 : W := mkw 0x37f830c40c643aa4 0x80dfe0c3103190ea 0xbffe71c61ce4ffff 0xfefff9c7187393ff

def z371 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d071c61ce40fcb 0x1e1b41c71873903f

def z372 : W := mkw 0x35a80000d2920010 0x04d6a000034a4800 0x793c0001e31f0013 0xb5e4f000078c7c00

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020000100180012 0xa400800004006000

def z374 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xfe027000fc00fc3d 0x73f809c003f003f0

def z375 : W := mkw 0x0000000040900000 0x0000000001024000 0x40000001e0f80030 0x050000000783e000

def z376 : W := mkw 0x275c7cd60c643aa4 0x889d71f3583190ea 0x87de7fc61ce4ffff 0x7e1f79ff187393ff

def z377 : W := mkw 0x3dab492000000000 0x08f6ad2480000000 0x3800000000000000 0x00e0000000000000

def z378 : W := mkw 0xbfffefb7b300c40a 0x0affffbedecc0310 0xffffffffe300000f 0xebffffffff8c0000

def z379 : W := mkw 0x5af3b1ed6cfcfbad 0x816bcec7b5b3f3ee 0xfee3f1f9fcf8f336 0xeffb8fc7e7f3e3cc

def z380 : W := mkw 0x00008209dbdf8579 0x44000208276f7e15 0x40000001ffff8ff0 0x1500000007fffe3f

def z381 : W := mkw 0x4000824961b9d749 0x410002092586e75d 0x40000001e3fffff0 0x15000000078fffff

def z382 : W := mkw 0x0254249600000000 0x0009509258000000 0x87fffffe0000000f 0xea1ffffff8000000

def z383 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfffffff031f001f 0xfefffffffc0c7c00

def z384 : W := mkw 0xa500580096002806 0x02940160025800a0 0x860070001c000000 0x021801c000700000

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000000040013 0x3400400000001000

def z386 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x813ffffe0000000f 0xaa04fffff8000000

def z387 : W := mkw 0x4807877b2129d749 0x41201e1dec84a75d 0x00038ffe0000ffcc 0x08000e3ff80003ff

def z388 : W := mkw 0x3fff6fb601010440 0x48fffdbed8040411 0xbffffffe03070ccf 0xfafffffff80c1c33

def z389 : W := mkw 0x0004861b01098549 0x400012186c042615 0x012d8e39031b8c1d 0xb004b638e40c6e30

def z390 : W := mkw 0x0250000008440020 0x0009400000211000 0x00d0000000e40002 0x0403400000039000

def z391 : W := mkw 0xaf53fa85b700ec0e 0x02bd4fea16dc03b0 0xffd3ffc7ff00fc3f 0xfbff4fff1ffc03f0

def z392 : W := mkw 0x7ffbe9ed60b8d309 0x09ffefa7b582e34c 0xfee3f1f9e0f8f336 0xeffb8fc7e783e3cc

def z393 : W := mkw 0x12f030c44cf43aa4 0x804bc0c31133d0ea 0xfef271c7fcfcffff 0xfffbc9c71ff3f3ff

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c201c000000006 0x6803080700000000

def z395 : W := mkw 0x025030840c4428a4 0x800940c2103110a2 0x861270061c04fcfd 0x721849c0187013f3

def z396 : W := mkw 0x0004041200000000 0x0000101048000000 0x012d8e3800000000 0x8004b638e0000000

def z397 : W := mkw 0x0250000008440020 0x0009400000211000 0x061000001c040001 0x1018400000701000

def z398 : W := mkw 0x37f8000008440020 0x00dfe00000211000 0x3ffc00001ce40033 0xf4fff00000739000

def z399 : W := mkw 0xfffbdb69fffeff3f 0x07ffef6da7fffbfc 0xfffffff9ffffff3f 0xffffffffe7fffffc

def z400 : W := mkw 0xbfffffb72500ec0e 0x0afffffedc9403b0 0xbffffffe0000fc0f 0xeafffffff80003f0

def z401 : W := mkw 0x0004861b01098549 0x400012186c042615 0x00018e3800000000 0x00000638e0000000

def z402 : W := mkw 0x37f8000000000000 0x00dfe00000000000 0x3ffc0001031f0013 0xf4fff000040c7c00

def z403 : W := mkw 0x025020c4086412a0 0x800940831021904a 0x00d201c600e4f3f6 0x6c034807180393cf

def z404 : W := mkw 0xad03da09b709ed4f 0x42b40f6826dc27b5 0xff03fe01ff1ffffd 0xf7fc0ff807fc7fff

def z405 : W := mkw 0x37fc0612dbd70470 0x44dff0184b6f5c11 0x7ffc0e07ffff0cfb 0xf5fff0381ffffc33

def z406 : W := mkw 0x58a3836961b8d709 0x01628e0da586e35c 0x79e38ff9e3f8ff3f 0xfde78e3fe78fe3fc

def z407 : W := mkw 0x58a3016860b85301 0x01628c05a182e14c 0x78e201f8e0f87322 0x4de38807e383e1cc

def z408 : W := mkw 0x1af321a400000000 0x006bcc8690000000 0xbef3f1fe0000000f 0xeafbcfc7f8000000

def z409 : W := mkw 0x58a7edff60b8d309 0x09629fb7fd82e34c 0xf8e3ffffe0f8f33e 0xefe38fffff83e3cc

def z410 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78218039e0f8f330 0x85e08600e783e3cc

def z411 : W := mkw 0xa5004a0093000402 0x02940128024c0010 0x01000e0003000000 0x00040038000c0000

def z412 : W := mkw 0x0004861b01098549 0x400012186c042615 0x012d8e39031b8316 0xac04b638e40c6e0c

def z413 : W := mkw 0x7dab8169f2bad319 0x05f6ae05a7caeb4c 0x79ef81f9e3fbf336 0xede7be07e78fefcc

def z414 : W := mkw 0x3fff6df600201200 0x08fffdb7d8008048 0xbffffffe00e0f33f 0xeefffffff80383cc

def z415 : W := mkw 0x0803480000000000 0x00200d2000000000 0x8003fe000000000c 0x02000ff800000000

def z416 : W := mkw 0x3fffefbf01098549 0x48ffffbefc042615 0xbffffffe00008fcf 0xeafffffff800023f

def z417 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x861070061ce4fff9 0x161841c0187393ff

def z418 : W := mkw 0x7fffedfffafed339 0x0dffffb7ffebfb4c 0xfffffffffffff33f 0xffffffffffffffcc

def z419 : W := mkw 0xad034800b2004002 0x02b40d2002c80100 0x78000000e0000000 0x01e0000003800000

def z420 : W := mkw 0xbffbda01ffd6ec3e 0x06ffef6807ff5bb0 0xffc3fe01ffe0fc3d 0xf3ff0ff807ff83f0

def z421 : W := mkw 0x80009201b700ec0e 0x0200024806dc03b0 0x41018e01ff00fc3d 0xb104063807fc03f0

def z422 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ee00001fcf80032 0xe5fb800007f3e000

def z423 : W := mkw 0x275c6c9600000000 0x089d71b258000000 0x873dfe3e0000000f 0xaa1cf7f8f8000000

def z424 : W := mkw 0x0000104004203a84 0x80000041001080ea 0x000000000000ffc0 0x00000000000003ff

def z425 : W := mkw 0x3fff7db60c4428a4 0x88fffdf6d83110a2 0xbffffffe1c040ccf 0xfafffffff8701033

def z426 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e181f9e0f80302 0x8de38607e783e00c

def z427 : W := mkw 0x3ffb480000000000 0x00ffed2000000000 0xbffffe000000000f 0xe2fffff800000000

def z428 : W := mkw 0x3ffb69a400000000 0x08ffeda690000000 0xbed271c60000000f 0x6afb49c718000000

def z429 : W := mkw 0x4000804960b8d309 0x010002012582e34c 0x40218039e0f8f336 0xad008600e783e3cc

def z430 : W := mkw 0x37fc041adadf0171 0x44dff0106b6b7c05 0x7ffc003fffff03f3 0xfdfff000fffffc0f

def z431 : W := mkw 0x12fc25b600000000 0x084bf096d8000000 0x86fe71fe0000000f 0x6a1bf9c7f8000000

def z432 : W := mkw 0x37f82084dad60030 0x04dfe082136b5800 0xfffe71c7ffff003f 0xfffff9c71ffffc00

def z433 : W := mkw 0x52f021ec48fc13a1 0x814bc087b123f04e 0x00f001fe00fc03c2 0x0c03c007f803f00f

def z434 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x79fc0001e3ff0002 0x85e7f000078ffc00

def z435 : W := mkw 0x37f8000040900000 0x00dfe00001024000 0x7ffc0001e0f80033 0xe5fff0000783e000

def z436 : W := mkw 0xbffffff7bf64feae 0x8affffffdefd93fa 0xffffffffffe4ffff 0xffffffffffff93ff

def z437 : W := mkw 0xad07de1bb709ed4f 0x42b41f786edc27b5 0xff03fe3fff00fffd 0xfbfc0ff8fffc03ff

def z438 : W := mkw 0x50a0016040b01200 0x014280058102c048 0x00c001c000e00000 0x0003000700038000

def z439 : W := mkw 0xfda3cb69f3b8d70b 0x03f68f2da7cee35c 0x79e38ff9e3f8f336 0xede78e3fe78fe3cc

def z440 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x861271c61c04ffcd 0x1a1849c7187013ff

def z441 : W := mkw 0x8803da012500ec0e 0x02200f68049403b0 0xf803fe01e000fc3c 0xe3e00ff8078003f0

def z442 : W := mkw 0x37fc25b600000000 0x08dff096d8000000 0x3ffc01fe00000003 0xe8fff007f8000000

def z443 : W := mkw 0xd8a3db6965b8ff0f 0x03628f6da596e3fc 0xf8e3fff9e0f8ff3e 0xefe38fffe783e3fc

def z444 : W := mkw 0x0000000800090141 0x4000000020002405 0x00000000001f03c0 0x0400000000007c0f

def z445 : W := mkw 0x025434de0c6d3be5 0xc00950d37831b4ef 0x86fe71fe1cffffff 0x7e1bf9c7f873ffff

def z446 : W := mkw 0x2758000000000000 0x009d600000000000 0x071c000000000001 0x001c700000000000

def z447 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3e00008fcf 0xa804f638f800023f

def z448 : W := mkw 0xa500da01b700ec0e 0x0294036806dc03b0 0xc7007e01ff00fc39 0x131c01f807fc03f0

def z449 : W := mkw 0x52f031ec4cfc3ba5 0x814bc0c7b133f0ee 0x86f271fe1cfcffff 0x7e1bc9c7f873f3ff

def z450 : W := mkw 0xfda3db61f7b0fe0e 0x03f68f6d87dec3f8 0xffc3ffc1ffe0fc3d 0xf3ff0fff07ff83f0

def z451 : W := mkw 0xaf53da01bf44ec2e 0x02bd4f6806fd13b0 0xffd3fe01ffe4fc3f 0xf7ff4ff807ff93f0

def z452 : W := mkw 0x0000820101008408 0x0000020804040210 0x01018e0103000000 0x80040638040c0000

def z453 : W := mkw 0x275c06129b470470 0x449d70184a6d1c11 0x071c0e061f070cc9 0x101c7038187c1c33

def z454 : W := mkw 0x2d03580004002804 0x00b40d60001000a0 0xbf03fe001c00fc3d 0xf2fc0ff8007003f0

def z455 : W := mkw 0x7dafcd7b60b8d309 0x09f6bf35ed82e34c 0x79ef8ff9e0f8f336 0xede7be3fe783e3cc

def z456 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xfe027001ff00fc30 0x53f809c007fc03f0

def z457 : W := mkw 0x37f80040daf61230 0x04dfe001036bd848 0x7ffe01c1fffff337 0xfdfff80707ffffcc

def z458 : W := mkw 0x7da3c96960b8d309 0x01f68f25a582e34c 0xffe3fff9e0f8f33f 0xefff8fffe783e3cc

def z459 : W := mkw 0xad03da01ffd6ec3e 0x06b40f6807ff5bb0 0xff03fe01fffffc3d 0xf7fc0ff807fffff0

def z460 : W := mkw 0x0004841b00088109 0x000012106c002204 0x013d8e3f0018831f 0xac04f638fc00620c

def z461 : W := mkw 0x7ffbb1edfefefbbd 0x85ffeec7b7fbfbee 0xfffff1ffffffffff 0xffffffc7ffffffff

def z462 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ed00000fce40033 0x75fb400003f39000

def z463 : W := mkw 0xfda3d969f6b8fb0f 0x03f68f65a7dae3ec 0xfee3f1f9fcf8f336 0xeffb8fc7e7f3e3cc

def z464 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f0cc9 0x9004f638fc0c7c33

def z465 : W := mkw 0x50a4877b41b99749 0x4142921ded06e65d 0x01fd8fff03ff8fdf 0xbc07f63ffc0ffe3f

def z466 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ec00001ffff0030 0x55fb000007fffc00

def z467 : W := mkw 0x3ffb4800dad60030 0x04ffed20036b5800 0xfffffe01ffff003f 0xf7fffff807fffc00

def z468 : W := mkw 0x58a7877b61b9d749 0x41629e1ded86e75d 0x79ef8ff9e3fbf336 0xede7be3fe78fefcc

def z469 : W := mkw 0x0000020001000400 0x0000000800040010 0x01000e0003000c09 0x10040038000c0030

def z470 : W := mkw 0x37f83084ded628b4 0x84dfe0c2137b58a2 0xfffc7007ffff0cfb 0xf7fff1c01ffffc33

def z471 : W := mkw 0x37f800009a460030 0x04dfe00002691800 0x3ffc00001f070003 0xf0fff000007c1c00

def z472 : W := mkw 0x3fff7df60c643aa4 0x88fffdf7d83190ea 0xbffffffe1ce0702f 0xeafffffff87381c0

def z473 : W := mkw 0x025020c4086412a0 0x800940831021904a 0x00c001c000e00000 0x0003000700038000

def z474 : W := mkw 0x58a3816160b0d208 0x01628e058582c348 0x78c381c1e0e0f034 0xe1e30e07078383c0

def z475 : W := mkw 0x18a3016000201200 0x00628c0580008048 0x38e381f800e0f336 0xece38e07e00383cc

def z476 : W := mkw 0x5af3a1ed68fcd3a9 0x816bce87b5a3f34e 0x78f381ffe0fcf3f6 0xede3ce07ff83f3cf

def z477 : W := mkw 0x5af331e46cf47aa4 0x816bccc791b3d1ea 0xfed271c6fce4ffff 0x7ffb49c71bf393ff

def z478 : W := mkw 0x37fc25b6dad60030 0x0cdff096db6b5800 0x7ffc01ffffff0033 0xfdfff007fffffc00

def z479 : W := mkw 0x0004041a00090141 0x4000101068002405 0x002c0038001b0000 0x0000b000e0006c00

def z480 : W := mkw 0x025030c4def63ab4 0x840940c3137bd8ea 0xc6d271c7ffffffff 0x7f1b49c71fffffff

def z481 : W := mkw 0x35a00000d2900000 0x00d68000034a4000 0x7fe00001fff80033 0xf5ff800007ffe000

def z482 : W := mkw 0x37fcb6dfdfffbffd 0xc4dff2db7f7ffeff 0xffffffffffffffff 0xffffffffffffffff

def z483 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfffffffefce0002f 0xebfffffffbf38000

def z484 : W := mkw 0x7ffb8129fadec139 0x05ffee04a7eb7b04 0x7ffd8039ffff0033 0xf5fff600e7fffc00

def z485 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f03c2 0x8c04f638fc0c7c0f

def z486 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x00e381f800f8f306 0x0c038e07e003e3cc

def z487 : W := mkw 0x58a7873b6199c549 0x41629e1ced866715 0x793d8e3fe31f8fdf 0xbde4f638ff8c7e3f

def z488 : W := mkw 0x025c249600000000 0x0809709258000000 0x001c000600000000 0x0000700018000000

def z489 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7fc00001ffe00031 0xf1ff000007ff8000

def z490 : W := mkw 0x02500000dad60030 0x04094000036b5800 0x46d00001ffff0033 0x751b400007fffc00

def z491 : W := mkw 0xbda3db21b700ec0e 0x02f68f6c86dc03b0 0xffe3fff9ff00fc3f 0xfbff8fffe7fc03f0

def z492 : W := mkw 0x0004861301018448 0x400012184c040611 0x011d8e0703078cdd 0xb00476381c0c1e33

def z493 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78c381f8e0e0f324 0x49e30e07e38383cc

def z494 : W := mkw 0x37f80000d2920010 0x04dfe000034a4800 0x7ffc0001e31b0003 0xe1fff000078c6c00

def z495 : W := mkw 0x0000208400000000 0x0000008210000000 0x800271c60000000c 0x0a0009c718000000

def z496 : W := mkw 0xbfffde1bffdfed7f 0x46ffff786fff7fb5 0xfffffe3fffffffff 0xfffffff8ffffffff

def z497 : W := mkw 0x275830849e4628b4 0x849d60c2127918a2 0x871c70061f070cc9 0x121c71c0187c1c33

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000600008fcc 0x080000001800023f

def z499 : W := mkw 0x000092010500ac0c 0x00000248041402b0 0x8703fe011f00fc3d 0xf21c0ff8047c03f0

def z500 : W := mkw 0x7fffedbf6098c109 0x09ffffb6fd826304 0xffffffffe018000f 0xebffffffff806000

def z501 : W := mkw 0x0000820101008408 0x0000020804040210 0x013d8e01031f8c1f 0xb404f638040c7e30

def z502 : W := mkw 0x0004061a01090541 0x4000101868042415 0x013c0e3e031f0fcb 0x1c04f038f80c7c3f

def z503 : W := mkw 0x0000800900088109 0x0000020024002204 0x0031803f001c8fdf 0xbc00c600fc00723f

def z504 : W := mkw 0x4803b1ed2428fb8d 0x81200ec7b490a3ee 0x8003f1fe0000ffcc 0x0a000fc7f80003ff

def z505 : W := mkw 0x3fffedbf00088109 0x08ffffb6fc002204 0xbfffffff0018831f 0xeefffffffc00620c

def z506 : W := mkw 0x000020c400201280 0x800000831000804a 0x000001c6000003c0 0x080000071800000f

def z507 : W := mkw 0xad07de1bb709ed4f 0x42b41f786edc27b5 0xff2ffe39ff1bfc3d 0xf3fcbff8e7fc6ff0

def z508 : W := mkw 0x0250000008440020 0x0009400000211000 0x06c000001ce00020 0x401b000000738000

def z509 : W := mkw 0x2d03480000000000 0x00b40d2000000000 0x39018e0000000000 0x80e4063800000000

def z510 : W := mkw 0xfff3fbedfffcffaf 0x83ffcfefb7fff3fe 0xfff3fffffffcffff 0xffffcffffffff3ff

def z511 : W := mkw 0xbffbca01fbd6c43a 0x06ffef2807ef5b10 0x7ffd8e01ffff0033 0xf5fff63807fffc00

def z512 : W := mkw 0x35a80000d2920010 0x04d6a000034a4800 0x78000000e0000000 0x01e0000003800000

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x012c0001031b0000 0x8004b000040c6c00

def z514 : W := mkw 0x18a3012000000000 0x00628c0480000000 0x38c201c000000000 0x40e3080700000000

def z515 : W := mkw 0xfda7df7bf7b9ff4f 0x43f69f7defdee7fd 0xffffffffffffffff 0xffffffffffffffff

def z516 : W := mkw 0x080380092008c109 0x00200e0024802304 0x78238039e018f336 0xede08e00e78063cc

def z517 : W := mkw 0x3fff7db604002804 0x08fffdf6d81000a0 0xbffffffe1c00fc3f 0xfafffffff87003f0

def z518 : W := mkw 0x0000820901098549 0x4000020824042615 0x00000001031b0000 0x00000000040c6c00

def z519 : W := mkw 0xad07ffb7b700ec0e 0x0ab41ffededc03b0 0xff03ffffff00fc3d 0xfbfc0ffffffc03f0

def z520 : W := mkw 0x58a7857b60b9d349 0x41629e15ed82e74d 0x78ff81ffe0fff3f6 0xede3fe07ff83ffcf

def z521 : W := mkw 0x3ffb69a4dad60030 0x0cffeda6936b5800 0xfec271c0fce00020 0x43fb09c703f38000

def z522 : W := mkw 0x80009209b709ed4f 0x4200024826dc27b5 0x40000001ff1ffff0 0x1500000007fc7fff

def z523 : W := mkw 0x37f8208400000000 0x00dfe08210000000 0xbffe71c60000000f 0xeafff9c718000000

def z524 : W := mkw 0x7ffb816960b8d309 0x01ffee05a582e34c 0x7fff81f9e0f8f337 0xedfffe07e783e3cc

def z525 : W := mkw 0x3daf4d3200000000 0x08f6bd34c8000000 0xbf2ffe380000000d 0xe2fcbff8e0000000

def z526 : W := mkw 0x5affa5ff60b8d309 0x096bfe97fd82e34c 0x78ff81ffe0f8f336 0xede3fe07ff83e3cc

def z527 : W := mkw 0x5af3a1ed60b8d309 0x016bce87b582e34c 0xfef3f1ffe0f8f33f 0xeffbcfc7ff83e3cc

def z528 : W := mkw 0x0004961b0509ad4d 0x400012586c1426b5 0x873ffe3f1f1fffff 0xfe1cfff8fc7c7fff

def z529 : W := mkw 0x0000000048d60030 0x0400000001235800 0x0000000000ff0000 0x040000000003fc00

def z530 : W := mkw 0x000010400c643aa4 0x80000041003190ea 0x000000001ce07020 0x00000000007381c0

def z531 : W := mkw 0x00000000dad60030 0x04000000036b5800 0x40000000fce00020 0x0100000003f38000

def z532 : W := mkw 0x12f8000048d60030 0x044be00001235800 0x78fc0001e0ff0032 0xe5e3f0000783fc00

def z533 : W := mkw 0x0000004000201200 0x0000000100008048 0x00c201c000e07020 0x40030807000381c0

def z534 : W := mkw 0x37f8000000000000 0x00dfe00000000000 0x3ec0000000000000 0x40fb000000000000

def z535 : W := mkw 0xaf5378c4be647aa6 0x82bd4de312f991ea 0xfec271c0fce07020 0x43fb09c703f381c0

def z536 : W := mkw 0x2f5378c40c643aa4 0x80bd4de3103190ea 0xbfd3ffc61ce4ffff 0xfeff4fff187393ff

def z537 : W := mkw 0xb7f89201ffd6ec3e 0x06dfe24807ff5bb0 0x7ffc0001fffffc33 0xf5fff00007fffff0

def z538 : W := mkw 0x0258000008460030 0x0409600000211800 0x001c000000070000 0x0000700000001c00

def z539 : W := mkw 0x000030c404203a84 0x800000c3101080ea 0x860271c61c00fffd 0x7a1809c7187003ff

def z540 : W := mkw 0xad03ca01b300c40a 0x02b40f2806cc0310 0x7f018e01ff000031 0xf1fc063807fc0000

def z541 : W := mkw 0xbdabda01f792ec1e 0x06f6af6807de4bb0 0xff2ffe01ff1bfc3d 0xf3fcbff807fc6ff0

def z542 : W := mkw 0x2504861b93098549 0x409412186e4c2615 0x7f3d8e3fff1f8fff 0xfdfcf638fffc7e3f

def z543 : W := mkw 0x37f8000000000000 0x00dfe00000000000 0x3ffc000000000003 0xe0fff00000000000

def z544 : W := mkw 0x37fc861bdbdf8579 0x44dff2186f6f7e15 0x7ffd8e39ffff0033 0xf5fff638e7fffc00

def z545 : W := mkw 0x7fff6df660b05200 0x09fffdb7d982c148 0xfffffffee0e0702f 0xebfffffffb8381c0

def z546 : W := mkw 0x35a80000dad60030 0x04d6a000036b5800 0x792c0001ffff0030 0x95e4b00007fffc00

def z547 : W := mkw 0xa504de1b9709ad4f 0x429413786e5c26b5 0x873dfe3f1f1f8fdf 0xbe1cf7f8fc7c7e3f

def z548 : W := mkw 0x0807efbf01098549 0x48201fbefc042615 0x8003fffe00008fcc 0x0a000ffff800023f

def z549 : W := mkw 0x00000040086412a0 0x800000010021904a 0x0000000000e403c0 0x040000000003900f

def z550 : W := mkw 0x37f81000ded62834 0x04dfe040037b58a0 0xfffe7001fffffc3f 0xf7fff9c007fffff0

def z551 : W := mkw 0x0004861b01098549 0x400012186c042615 0x01018e3f03008fdd 0xb8040638fc0c023f

def z552 : W := mkw 0x0004b6df0529bfcd 0xc00012db7c14a6ff 0x8003fffe0000ffcc 0x0a000ffff80003ff

def z553 : W := mkw 0x0004041200010040 0x4000101048000401 0x001c0006000700c0 0x0000700018001c03

def z554 : W := mkw 0x3fffffff0d6dbfed 0xc8fffffffc35b6ff 0xbfffffff1fffffff 0xfefffffffc7fffff

def z555 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78e201c1e0f87032 0xe5e388070783e1c0

def z556 : W := mkw 0x025020c4086412a0 0x800940831021904a 0x00d001c600e48fdf 0x3c0340071803923f

def z557 : W := mkw 0xbda3da01f790ec0e 0x02f68f6807de43b0 0xffe3fe01fff8fc3f 0xf7ff8ff807ffe3f0

def z558 : W := mkw 0x37fc6c9600000000 0x08dff1b258000000 0xbffc7e060000000b 0xe2fff1f818000000

def z559 : W := mkw 0x025020c400201200 0x0009408310008048 0x86d271c600e0f33f 0x6e1b49c7180383cc

def z560 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x00d001c61ce4fff2 0x1c034007187393ff

def z561 : W := mkw 0x0000820901088509 0x0000020824042214 0x01218e3903188f1f 0xbc048638e40c623c

def z562 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce0702f 0x6a1b49c7187381c0

def z563 : W := mkw 0xa500da019700ac0e 0x02940368065c02b0 0x8701fe011f008c1d 0xb21c07f8047c0230

def z564 : W := mkw 0x50a0816940b89309 0x01428205a502e24c 0x00e181f900f88316 0xac038607e403e20c

def z565 : W := mkw 0xad035a0097002c06 0x02b40d68025c00b0 0xbf03fe001f000c0d 0xf2fc0ff8007c0030

def z566 : W := mkw 0xa7507ac49f643ea6 0x829d41eb127d90fa 0x87d27fc61fe4ffff 0x7e1f49ff187f93ff

def z567 : W := mkw 0x3fffefbfdbdf8579 0x4cffffbeff6f7e15 0xffffffffffff8fff 0xfffffffffffffe3f

def z568 : W := mkw 0x58a7857b60b8d309 0x01629e15ed82e34c 0x79ff8fffe0f8f33f 0xede7fe3fff83e3cc

def z569 : W := mkw 0x58a3012060904000 0x01628c0481824100 0x78000000e0000000 0x01e0000003800000

def z570 : W := mkw 0x0000800900088109 0x0000020024002204 0x0001803800008304 0x08000600e000020c

def z571 : W := mkw 0x10a00000dad60030 0x04428000036b5800 0x78e00001ffff0032 0xf5e3800007fffc00

def z572 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000001c000031 0x7018000000700000

def z573 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce47ce9 0x521b49c7187391f3

def z574 : W := mkw 0x10a0000040900000 0x0042800001024000 0x79fc0001e3ff0033 0xf5e7f000078ffc00

def z575 : W := mkw 0xbfff7db6b6006806 0x0afffdf6dad801a0 0xfffffffefc00702f 0xebfffffffbf001c0

def z576 : W := mkw 0xd8a39369f7b8ff0f 0x03628e4da7dee3fc 0x78e381f9fff8ff36 0xfde38e07e7ffe3fc

def z577 : W := mkw 0x275c6c969a460030 0x0c9d71b25a691800 0x871c7e061f070009 0x121c71f8187c1c00

def z578 : W := mkw 0x2500480000000000 0x0094012000000000 0x87007e0000000009 0x021c01f800000000

def z579 : W := mkw 0x8004961bb709ed4f 0x420012586edc27b5 0x413d8e3fff1fffff 0xbd04f638fffc7fff

def z580 : W := mkw 0x0000004000201200 0x0000000100008048 0x00c001c000e00302 0x0c0300070003800c

def z581 : W := mkw 0x025030840c4428a4 0x800940c2103110a2 0x860070001c000000 0x021801c000700000

def z582 : W := mkw 0x35ac861bd39b8559 0x44d6b2186f4e6e15 0x792d8e39e31b0000 0x81e4b638e78c6c00

def z583 : W := mkw 0xfda3db29f798ed0f 0x03f68f6ca7de63b4 0xff23fe39ff18fc3d 0xf3fc8ff8e7fc63f0

def z584 : W := mkw 0xfffffffff7b8ff0f 0x0bffffffffdee3fc 0xfffffffffff8ff3f 0xffffffffffffe3fc

def z585 : W := mkw 0x080380012000c008 0x00200e0004800300 0x78018001e0000000 0x81e0060007800000

def z586 : W := mkw 0x000030c40c643aa4 0x800000c3103190ea 0x800271c61ce4fffc 0x1e0009c7187393ff

def z587 : W := mkw 0x7ffb0160faf65230 0x05ffec0583ebd948 0x7ec201c0fce07020 0x41fb080703f381c0

def z588 : W := mkw 0x2d038001b200c008 0x00b40e0006c80300 0x7f038001ff00f035 0xf1fc0e0007fc03c0

def z589 : W := mkw 0x77f88049fafed339 0x05dfe20127ebfb4c 0x7ffc0001fffff333 0xf5fff00007ffffcc

def z590 : W := mkw 0xad03ca01b300c40a 0x02b40f2806cc0310 0x79018e01e3008c1d 0xb1e40638078c0230

def z591 : W := mkw 0x2d076db600000000 0x08b41db6d8000000 0xbf03fffe0000000d 0xeafc0ffff8000000

def z592 : W := mkw 0x37fc6c96dad60030 0x0cdff1b25b6b5800 0xfffc7e07ffff003b 0xf7fff1f81ffffc00

def z593 : W := mkw 0x0254b6df0d6dbfed 0xc00952db7c35b6ff 0x86d3fffe1ce4ffff 0x7e1b4ffff87393ff

def z594 : W := mkw 0x3ffb69a400000000 0x08ffeda690000000 0xbffe71c000000003 0xe2fff9c700000000

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x0021803800000006 0xa8008600e0000000

def z596 : W := mkw 0x0004861b01098549 0x400012186c042615 0x00218e3f00188fde 0xac008638fc00623f

def z597 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x80d271c600e4ffce 0x0e0349c7180393ff

def z598 : W := mkw 0x3fffedb72000c008 0x08ffffb6dc800300 0xffffffffe000f03f 0xebffffffff8003c0

def z599 : W := mkw 0x080382012100c408 0x00200e0804840310 0x79038e01e300fc3d 0xf1e40e38078c03f0

def z600 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x782381f9e018f304 0x89e08e07e78063cc

def z601 : W := mkw 0x0807efbf01098549 0x48201fbefc042615 0x813fffff031f8fdf 0xbe04fffffc0c7e3f

def z602 : W := mkw 0x000010400c643aa4 0x80000041003190ea 0x860270001ce4fffd 0x761809c0007393ff

def z603 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031b000f 0xa804f638fc0c6c00

def z604 : W := mkw 0x40008049fafed339 0x0500020127ebfb4c 0x40000001fffff330 0x1500000007ffffcc

def z605 : W := mkw 0x3dafcf3b01098549 0x48f6bf3cec042615 0x392d8e39031b0000 0x80e4b638e40c6c00

def z606 : W := mkw 0xaf5ffe97b700ec0e 0x0abd7ffa5edc03b0 0xff1ffe07ff00fc3d 0xf3fc7ff81ffc03f0

def z607 : W := mkw 0x35a80000d2920010 0x04d6a000034a4800 0x7f2c0001ff1b0031 0xf1fcb00007fc6c00

def z608 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x07fc00001fff0003 0x141ff000007ffc00

def z609 : W := mkw 0x10a0004040b01200 0x004280010102c048 0x78e201c1e0f8f336 0xede388070783e3cc

def z610 : W := mkw 0x4a53b1ed2c6cfbad 0x81294ec7b4b1b3ee 0x86d3f1fe1ce4ffff 0x7e1b4fc7f87393ff

def z611 : W := mkw 0x0004861b01098549 0x400012186c042615 0x00118e3e00048fdf 0x3c004638f800123f

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x000200000000f034 0x60000800000003c0

def z613 : W := mkw 0x8803580024006806 0x02200d60009001a0 0x8002700000007000 0x020009c0000001c0

def z614 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c01ce0fc3d 0x721b09c7007383f0

def z615 : W := mkw 0xad07ce1bb309c54b 0x42b41f386ecc2715 0x793d8e3fe31f8fdf 0xbde4f638ff8c7e3f

def z616 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78c201c1e0f8f330 0x45e308070783e3cc

def z617 : W := mkw 0x58a381296098c109 0x01628e04a5826304 0x78e18039e0f80032 0xe5e38600e783e000

def z618 : W := mkw 0x0254a6df096d97e9 0xc009529b7c25b65f 0x01fd8fff03ff8fdf 0xbc07f63ffc0ffe3f

def z619 : W := mkw 0x0000000008440020 0x0000000000211000 0x000000001ce40030 0x1400000000739000

def z620 : W := mkw 0x0a577df60c643aa4 0x88295df7d83190ea 0x86d3fffe1ce4ffff 0x7e1b4ffff87393ff

def z621 : W := mkw 0x10a0000040900000 0x0042800001024000 0x00e0000000f80002 0x040380000003e000

def z622 : W := mkw 0x400080492028d309 0x010002012480a34c 0x000000000000f300 0x00000000000003cc

def z623 : W := mkw 0x58a3016840b81301 0x01628c05a102e04c 0x38e381f800f80306 0xece38e07e003e00c

def z624 : W := mkw 0x2500820193008408 0x00940208064c0210 0x7f018e01ff008c3d 0xf1fc063807fc0230

def z625 : W := mkw 0x0004041a00090141 0x4000101068002405 0x0000003e000003c0 0x08000000f800000f

def z626 : W := mkw 0x35a8000000000000 0x00d6a00000000000 0x392c000000000000 0x80e4b00000000000

def z627 : W := mkw 0x275cee9f01098549 0x489d73ba7c042615 0x873dfe3f031f8fdf 0xbe1cf7f8fc0c7e3f

def z628 : W := mkw 0x3ffb69a4dad60030 0x0cffeda6936b5800 0xfffe71c1ffff0033 0xf7fff9c707fffc00

def z629 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7efc0000fcff0022 0x45fbf00003f3fc00

def z630 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbf3dfe3e00000009 0x82fcf7f8f8000000

def z631 : W := mkw 0x10a0012000000000 0x0042800480000000 0x00e001f800000002 0x08038007e0000000

def z632 : W := mkw 0x0000104004203a04 0x00000041001080e8 0x86c271c01ce0ff3f 0x7e1b09c7007383fc

def z633 : W := mkw 0x0000804900289309 0x000002012400a24c 0x00e381f900f8f336 0xec038e07e403e3cc

def z634 : W := mkw 0x12f8000048d60030 0x044be00001235800 0x00c0000000e00000 0x0003000000038000

def z635 : W := mkw 0x37f830c4def63ab4 0x84dfe0c3137bd8ea 0xfec271c0fce07020 0x43fb09c703f381c0

def z636 : W := mkw 0x4000804960b8d309 0x010002012582e34c 0x40c201c1e0f8f336 0x6d0308070783e3cc

def z637 : W := mkw 0x4000016800281301 0x01000005a000a04c 0x000001f800000300 0x08000007e000000c

def z638 : W := mkw 0x8a53fac52d64feae 0x82294feb14b593fa 0x86d3ffc61ce4ffff 0x7e1b4fff187393ff

def z639 : W := mkw 0x00001040def63ab4 0x84000041037bd8ea 0x40000001fffffff0 0x1500000007ffffff

def z640 : W := mkw 0x12fc25f6086412a0 0x884bf097d821904a 0x00fc01fe00e403c2 0x0c03f007f803900f

def z641 : W := mkw 0xbffb79a4b6006806 0x0affede692d801a0 0xfec271c0fc007020 0x43fb09c703f001c0

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000008c1d 0x3000000000000230

def z643 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfde7fc600000009 0x42ff79ff18000000

def z644 : W := mkw 0x58a391696cfcfbad 0x81628e45a5b3f3ee 0x78e381f9fcfcfff6 0xfde38e07e7f3f3ff

def z645 : W := mkw 0x275800009a460030 0x049d600002691800 0x07dc00001fe70033 0x741f7000007f9c00

def z646 : W := mkw 0x275c861b9b4f8579 0x449d72186e6d3e15 0x073d8e3f1f1f8fdf 0xbc1cf638fc7c7e3f

def z647 : W := mkw 0x8807de1b2509ed4f 0x42201f786c9427b5 0x8003fe3e0000ffcc 0x0a000ff8f80003ff

def z648 : W := mkw 0x0254a69f01098549 0x4009529a7c042615 0x87ffffff031f8fdf 0xfe1ffffffc0c7e3f

def z649 : W := mkw 0x0000820101008408 0x0000020804040210 0x01118e0703048fdf 0xbc0446381c0c123f

def z650 : W := mkw 0x10a0000000000000 0x0042800000000000 0x38e0000000000002 0xe0e3800000000000

def z651 : W := mkw 0xa7585a009f462c36 0x069d6168027d18b0 0x871c7e001f070c09 0x121c71f8007c1c30

def z652 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0000fce00023 0xe1fff00003f38000

def z653 : W := mkw 0x0250b0cd0c6cbbad 0x800942c33431b2ee 0x86f3f1ff1cfcffff 0xfe1bcfc7fc73f3ff

def z654 : W := mkw 0xad03ca01b300c40a 0x02b40f2806cc0310 0x79038e01e300f034 0xe1e40e38078c03c0

def z655 : W := mkw 0x58a7873b6199c549 0x41629e1ced866715 0x792d8e39e31b0000 0x81e4b638e78c6c00

def z656 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78c201c0e0e0f336 0x6de30807038383cc

def z657 : W := mkw 0x7ffb69e460b05200 0x09ffeda79182c148 0xfec271c0e0e07020 0x43fb09c7038381c0

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000008316 0x2c0000000000020c

def z659 : W := mkw 0x0000100004002804 0x00000040001000a0 0x000000001c00fc30 0x10000000007003f0

def z660 : W := mkw 0x480381692028d309 0x01200e05a480a34c 0x780381f9e000f334 0xe9e00e07e78003cc

def z661 : W := mkw 0x80009241bf64feae 0x8200024906fd93fa 0x40000001ffe4fff0 0x1500000007ff93ff

def z662 : W := mkw 0xc803db692528ff0f 0x03200f6da494a3fc 0x8003fff80000ff0c 0x0a000fffe00003fc

def z663 : W := mkw 0x8000120097002c06 0x02000048025c00b0 0x000000001f000c00 0x10000000007c0030

def z664 : W := mkw 0x37fc6db600000000 0x08dff1b6d8000000 0x87fc7ffe0000000b 0x0a1ff1fff8000000

def z665 : W := mkw 0x80005a0005002c06 0x02000168001400b0 0x80007e0000000c08 0x020001f800000030

def z666 : W := mkw 0x12f8000048d60030 0x044be00001235800 0x01fc000103ff0013 0xb407f000040ffc00

def z667 : W := mkw 0x08077df604203a84 0x88201df7d81080ea 0x8003fffe0000ffcc 0x0a000ffff80003ff

def z668 : W := mkw 0x2d03480000000000 0x00b40d2000000000 0xbe02700000000000 0x42f809c000000000

def z669 : W := mkw 0x18a7053200000000 0x00629c14c8000000 0x39ff8ffe0000000f 0xe8e7fe3ff8000000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000048fd0 0x140000000000123f

def z671 : W := mkw 0x3fffefbf01098549 0x48ffffbefc042615 0xbfffffff031b000f 0xeafffffffc0c6c00

def z672 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7fdc0000ffe70021 0x51ff700003ff9c00

def z673 : W := mkw 0xbdafdf33b700ec0e 0x0af6bf7ccedc03b0 0xff2ffe39ff00fc3d 0xf3fcbff8e7fc03f0

def z674 : W := mkw 0x0807861b2109c549 0x40201e186c842715 0x793f8e3fe31fffff 0xfde4fe38ff8c7fff

def z675 : W := mkw 0xb7f85a00dfd62c36 0x06dfe168037f58b0 0xfffc7e01ffff0c3b 0xf7fff1f807fffc30

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x011c000003070001 0x10047000000c1c00

def z677 : W := mkw 0x3fff6dbe00090141 0x48fffdb6f8002405 0xbffffffe001f03cf 0xeefffffff8007c0f

def z678 : W := mkw 0x0250000000000000 0x0009400000000000 0x06d0000000000003 0x601b400000000000

def z679 : W := mkw 0x0004861b01098549 0x400012186c042615 0x011c0e07031f8fd9 0x140470381c0c7e3f

def z680 : W := mkw 0x2d03c8012000c008 0x00b40f2004800300 0xff03fe01e000f03d 0xe3fc0ff8078003c0

def z681 : W := mkw 0x2508000092020010 0x0494200002480800 0x010c000003030000 0x00043000000c0c00

def z682 : W := mkw 0x0250308404002804 0x000940c2101000a0 0x86d271c61c00fc3f 0x7a1b49c7187003f0

def z683 : W := mkw 0xbfff7fb697002c06 0x0afffdfeda5c00b0 0xbffffffe1f000c0f 0xfafffffff87c0030

def z684 : W := mkw 0x58a381296098c109 0x01628e04a5826304 0x78218039e0188316 0xade08600e780620c

def z685 : W := mkw 0x10a0000040900000 0x0042800001024000 0x78c00000e0e00020 0x41e3000003838000

def z686 : W := mkw 0x18a3012000000000 0x00628c0480000000 0x3821803800000000 0x80e08600e0000000

def z687 : W := mkw 0x080390012400e80c 0x00200e40049003a0 0xfe03f001fc00fc3d 0xf3f80fc007f003f0

def z688 : W := mkw 0x2500000000000000 0x0094000000000000 0x3f00000000000001 0xe0fc000000000000

def z689 : W := mkw 0x4250b0cd6cfcfbad 0x810942c335b3f3ee 0xc6d271c7fcfcffff 0x7f1b49c71ff3f3ff

def z690 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce473e2 0x4e1b49c7187391cf

def z691 : W := mkw 0x18a3812900088109 0x00628e04a4002204 0x38e381f900188316 0xece38e07e400620c

def z692 : W := mkw 0x58a3916964b8fb0d 0x01628e45a592e3ec 0xfee3f1f9fcf8ff3f 0xfffb8fc7e7f3e3fc

def z693 : W := mkw 0x275c6c9600000000 0x089d71b258000000 0x87de7fc60000000f 0x6a1f79ff18000000

def z694 : W := mkw 0x12f8000048d60030 0x044be00001235800 0x06fc00001cff0033 0x741bf0000073fc00

def z695 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0x79018e01ff00fc30 0x91e4063807fc03f0

def z696 : W := mkw 0x37f8000092000000 0x00dfe00002480000 0x7ffc0001ff000033 0xf1fff00007fc0000

def z697 : W := mkw 0xad03fac5b720fe8e 0x82b40feb16dc83fa 0xff03ffc7ff00fffd 0xfbfc0fff1ffc03ff

def z698 : W := mkw 0x10ac053200000000 0x0842b014c8000000 0x002c003800000000 0x0000b000e0000000

def z699 : W := mkw 0x0004061201010440 0x4000101848040411 0x013c0e07031f0cdb 0xb404f0381c0c7c33

def z700 : W := mkw 0x18a7873b01098549 0x40629e1cec042615 0x39ff8fff031f8fdf 0xfce7fe3ffc0c7e3f

def z701 : W := mkw 0x12fc041a48df0171 0x444bf01069237c05 0x00fc003e00ff03c2 0x0c03f000f803fc0f

def z702 : W := mkw 0x12f821a400000000 0x084be08690000000 0x00c001c000000000 0x0003000700000000

def z703 : W := mkw 0x37f830c4def63ab4 0x84dfe0c3137bd8ea 0xfffe71c1ffff7033 0xf7fff9c707fffdc0

def z704 : W := mkw 0x0004861b01098549 0x400012186c042615 0x012d8e3f031b8fcc 0x8804b638fc0c6e3f

def z705 : W := mkw 0x025010000c442824 0x00094040003110a0 0x86d270001ce4fc3f 0x761b49c0007393f0

def z706 : W := mkw 0x80009201ffd6ec3e 0x0600024807ff5bb0 0x40000001fffffc30 0x1500000007fffff0

def z707 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe1c00003f 0xfafffffff8700000

def z708 : W := mkw 0x08076db6dad60030 0x0c201db6db6b5800 0xc003ffffffff003c 0x1f000ffffffffc00

def z709 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0x87fffffe0000000f 0x0a1ffffff8000000

def z710 : W := mkw 0xad03da09b708ed0f 0x02b40f6826dc23b4 0xff03fe39ff00ff3d 0xfbfc0ff8e7fc03fc

def z711 : W := mkw 0x0004861b01098549 0x400012186c042615 0x793d8e3fe31f8fff 0xfde4f638ff8c7e3f

def z712 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7fdc0001ffff0031 0x55ff700007fffc00

def z713 : W := mkw 0x0000104004203a04 0x00000041001080e8 0x86d271c61ce4ffff 0x7e1b49c7187393ff

def z714 : W := mkw 0x0a576db608440020 0x08295db6d8211000 0x86d3fffe1ce4003f 0x7e1b4ffff8739000

def z715 : W := mkw 0x50a0816960b8d309 0x01428205a582e34c 0x78e001f9e0f8f332 0xede38007e783e3cc

def z716 : W := mkw 0x3fff6db608440020 0x08fffdb6d8211000 0xbffffffe1ce48fff 0xfefffffff873923f

def z717 : W := mkw 0x0004861b01098549 0x400012186c042615 0x073d8e3f1f1f8fff 0xfc1cf638fc7c7e3f

def z718 : W := mkw 0x0004041200000000 0x0000101048000000 0x013d8e3f031f8fdf 0xbc04f638fc0c7e3f

def z719 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001ffff0022 0xc5fff00007fffc00

def z720 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe00008c1f 0xfafffffff8000230

def z721 : W := mkw 0x3ffbebad01098549 0x48ffefaeb4042615 0xbec271c1031f8fd0 0x56fb09c7040c7e3f

def z722 : W := mkw 0xed03db29b708ed0f 0x03b40f6ca6dc23b4 0xff03fe39ff00fc3d 0xf3fc0ff8e7fc03f0

def z723 : W := mkw 0x37fc861bdbdf8579 0x44dff2186f6f7e15 0x7ec18e3efce08fec 0x49fb0638fbf3823f

def z724 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff01fe01ff00fc39 0x93fc07f807fc03f0

def z725 : W := mkw 0x37f82084dad600b0 0x84dfe082136b5802 0x7ffc0007ffff00f3 0xf5fff0001ffffc03

def z726 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfdffffe0000000d 0x4aff7ffff8000000

def z727 : W := mkw 0xad075c1ab6096947 0x42b41d706ad825a5 0xfe3e703efc1f73e2 0x4ff8f9c0fbf07dcf

def z728 : W := mkw 0x35a830c4d6b23a94 0x84d6a0c3135ac8ea 0xf92e71c7e31bffcc 0x8be4b9c71f8c6fff

def z729 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xffffffffe3ff000f 0xefffffffff8ffc00

def z730 : W := mkw 0xad03da09b709ed4f 0x42b40f6826dc27b5 0xff03fe01ff00fffd 0xf3fc0ff807fc03ff

def z731 : W := mkw 0xf5a05b68d7b83f07 0x03d6816da35ee0fc 0x87e07ff81ff80f0b 0x1e1f81ffe07fe03c

def z732 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xffffffffffff8fff 0xfffffffffffffe3f

def z733 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe00000009 0xc2fffffff8000000

def z734 : W := mkw 0x2d03580096002804 0x00b40d60025800a0 0xff03fe01ff00fc3d 0xf3fc0ff807fc03f0

def z735 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x79e381f9e3f8f337 0xfde78e07e78fe3cc

def z736 : W := mkw 0x58a7077261b15640 0x41629c1dc986c559 0x79de0fc6e3e77ce9 0x51e7783f1b8f9df3

def z737 : W := mkw 0xad03da09b709ed4f 0x42b40f6826dc27b5 0xff13fe07ff1fffff 0xfffc4ff81ffc7fff

def z738 : W := mkw 0x250092019700ac0c 0x00940248065c02b0 0xff03fe01ff00fc3d 0xf3fc0ff807fc03f0

def z739 : W := mkw 0xad035a00b7006c06 0x02b40d6802dc01b0 0xfe027e00fc007c28 0x43f809f803f001f0

def z740 : W := mkw 0x9afbda016dd6ec3e 0x066bef6805b75bb0 0x80fffe0000fffc0e 0x0603fff80003fff0

def z741 : W := mkw 0x000092490529bfcd 0xc00002492414a6ff 0x00000001031fffd0 0x14000000040c7fff

def z742 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce4ffcf 0x1e1b49c7187393ff

def z743 : W := mkw 0x58a3836961b8d709 0x01628e0da586e35c 0x79ff8ff9e3ffff3f 0xfde7fe3fe78ffffc

def z744 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0007ffff003f 0xfdfff0001ffffc00

def z745 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfffffffffffb002f 0xebffffffffffec00

def z746 : W := mkw 0x2f576c9600000000 0x00bd5db258000000 0xbffffffe0000000f 0xeafffffff8000000

def z747 : W := mkw 0x3ffb79e4def63ab4 0x8cffede7937bd8ea 0xfec271c0fce07020 0x43fb09c703f381c0

def z748 : W := mkw 0x3fff6db640920010 0x0cfffdb6d9024800 0xbffffffe001b000f 0xeafffffff8006c00

def z749 : W := mkw 0x12fc25f648f612b0 0x8c4bf097d923d84a 0x00fc01fe00ff03c2 0x0c03f007f803fc0f

def z750 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78f381ffe0f8f33f 0xede3ce07ff83e3cc

def z751 : W := mkw 0x37fc6db600000000 0x08dff1b6d8000000 0x87fdfffe0000000f 0xaa1ff7fff8000000

def z752 : W := mkw 0x58a3016860b85301 0x01628c05a182e14c 0x78c201f8e0e07320 0x49e30807e38381cc

def z753 : W := mkw 0x3fff6db692000000 0x08fffdb6da480000 0xfffffffefc00002f 0xebfffffffbf00000

def z754 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f8fce 0x8c04f638fc0c7e3f

def z755 : W := mkw 0x3fff6db648d60030 0x0cfffdb6d9235800 0xffffffffe0ff003f 0xefffffffff83fc00

def z756 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfffffff0018001f 0xeefffffffc006000

def z757 : W := mkw 0x37f86884dad60030 0x0cdfe1a2136b5800 0xfffc7001ffff0033 0xf7fff1c007fffc00

def z758 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff13fe07ff00fc3f 0xfbfc4ff81ffc03f0

def z759 : W := mkw 0x37f82084dad60030 0x04dfe082136b5800 0x7ffc01c7ffff0033 0xfdfff0071ffffc00

def z760 : W := mkw 0x3fff6db640900000 0x08fffdb6d9024000 0xfffffffee0e0002f 0xebfffffffb838000

def z761 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c61ce0fffe 0x6e1b09c7187383ff

def z762 : W := mkw 0x37f82084dad60030 0x04dfe082136b5800 0xfffe71c7ffff8fff 0xfffff9c71ffffe3f

def z763 : W := mkw 0x3daf6db600000000 0x08f6bdb6d8000000 0xb93ffffe0000000f 0xaae4fffff8000000

def z764 : W := mkw 0xfda7cf3bf399c54b 0x43f69f3cefce6715 0x792d8e39e31b0000 0x81e4b638e78c6c00

def z765 : W := mkw 0xa75c7e969f462c36 0x0e9d71fa5a7d18b0 0x871c7e061f070c09 0x121c71f8187c1c30

def z766 : W := mkw 0x275c6c9600000000 0x089d71b258000000 0x87fffffe0000000f 0xea1ffffff8000000

def z767 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff3ffe07ff1fffff 0xfffcfff81ffc7fff

def z768 : W := mkw 0x275c36969f472cf4 0xc49d70da5a7d1cb3 0x871c7e061f070cc9 0x121c71f8187c1c33

def z769 : W := mkw 0x5af3b1ad6cdce9ad 0x816bcec6b5b373a6 0xfe31f03ffc1c0cc9 0x93f8c7c0fff07033

def z770 : W := mkw 0xaf53eac5bb64d6aa 0x82bd4fab16ed935a 0x79d18fc7e3e403c2 0x8de7463f1f8f900f

def z771 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78c381f9e0f8f334 0x4de30e07e783e3cc

def z772 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001ffff8337 0xfdfff00007fffe0c

def z773 : W := mkw 0x080380492028d309 0x00200e012480a34c 0x78e381f9e0f8f336 0xede38e07e783e3cc

def z774 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfffffff0300001f 0xfafffffffc0c0000

def z775 : W := mkw 0x3daf5d720c643aa4 0x88f6bd75c83190ea 0x392d8e381ce4fff0 0x94e4b638e07393ff

def z776 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78c381f8e0e07024 0x49e30e07e38381c0

def z777 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0xfed271c7fce4ffff 0xfffb49c71ff393ff

def z778 : W := mkw 0x92fcb7b7b700ec0e 0x0a4bf2dededc03b0 0x40fc01ffff00fc32 0x1903f007fffc03f0

def z779 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c61ce0fffd 0x7a1b09c7187383ff

def z780 : W := mkw 0x2f5f6db600000000 0x08bd7db6d8000000 0x87dffffe0000000f 0x6a1f7ffff8000000

def z781 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x79ff81ffe3ffffff 0xfde7fe07ff8fffff

def z782 : W := mkw 0x2d03d8012400e80c 0x00b40f60049003a0 0xff03fe01fc00fc3d 0xf3fc0ff807f003f0

def z783 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbed3fffe0000000f 0x6afb4ffff8000000

def z784 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce4fff2 0x5e1b49c7187393ff

def z785 : W := mkw 0x0004861b01098549 0x400012186c042615 0x01ff8fff031f8fdf 0xfc07fe3ffc0c7e3f

def z786 : W := mkw 0xad03da09b708ed0f 0x02b40f6826dc23b4 0xff23fe39ff18fc3d 0xf3fc8ff8e7fc63f0

def z787 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86fe71c61cffffff 0x7e1bf9c71873ffff

def z788 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffe0001fffff037 0xf5fff80007ffffc0

def z789 : W := mkw 0x3ffb4920dad60030 0x04ffed24836b5800 0xfffffff9ffff003f 0xffffffffe7fffc00

def z790 : W := mkw 0x37fc2496dad60030 0x04dff0925b6b5800 0xffffffffffff003f 0xfffffffffffffc00

def z791 : W := mkw 0x3fff6db648d40020 0x08fffdb6d9235000 0xfffffffffcfc003f 0xfffffffffff3f000

def z792 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c71fffffff 0x7e1b49c71c7fffff

def z793 : W := mkw 0x0a576db600000000 0x08295db6d8000000 0x80d3fffe0000000e 0x0a034ffff8000000

def z794 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f8ff3f 0xfde38e07e783e3fc

def z795 : W := mkw 0x2d0f6db600000000 0x08b43db6d8000000 0x810ffffe0000000c 0x0a043ffff8000000

def z796 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001ffff0021 0xd1fff00007fffc00

def z797 : W := mkw 0xa7547e969f452ce6 0xc29d51fa5a7d14b3 0x871c7e061f070cc9 0x121c71f8187c1c33

def z798 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbefffffe0000000e 0x4afbfffff8000000

def z799 : W := mkw 0x3fff6db692000000 0x08fffdb6da480000 0xffffffffff1f003f 0xfffffffffffc7c00

def z800 : W := mkw 0x37fc249600000000 0x00dff09258000000 0xbffffffe0000000f 0xeafffffff8000000

def z801 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x87de71c61fe7ffff 0x7e1f79c7187f9fff

def z802 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78ff81f9e0fff336 0xede3fe07e783ffcc

def z803 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78c381f8e0e0f336 0x6de30e07e38383cc

def z804 : W := mkw 0x3fff6db620004000 0x08fffdb6d8800100 0xfffffffee000702f 0xebfffffffb8001c0

def z805 : W := mkw 0x18a381216090c008 0x00628e0485824300 0x78e381f9e0f8f036 0xede38e07e783e3c0

def z806 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78e381f8e0e0f336 0xede38e07e38383cc

def z807 : W := mkw 0x35a00000d2900000 0x00d68000034a4000 0x7ffc0001ffff0033 0xf5fff00007fffc00

def z808 : W := mkw 0x2d03c801b200c008 0x00b40f2006c80300 0xff03fe01ff00f03d 0xf3fc0ff807fc03c0

def z809 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7fec0001ffff0030 0xd5ffb00007fffc00

def z810 : W := mkw 0x12fc25b600000000 0x084bf096d8000000 0x87fffffe0000000f 0xea1ffffff8000000

def z811 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78c381f9e0e0f334 0xe9e30e07e78383cc

def z812 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001ffff0003 0x95fff00007fffc00

def z813 : W := mkw 0x0254b6df0d6dbfed 0xc00952db7c35b6ff 0x87effff91ffb7020 0xc21fbfffe47fedc0

def z814 : W := mkw 0x37f821a4dad60030 0x0cdfe086936b5800 0x7ffc01c1ffff0033 0xf5fff00707fffc00

def z815 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffe01c1ffff0037 0xfdfff80707fffc00

def z816 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x803ffffe0000000e 0x0a00fffff8000000

def z817 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8013fffe0000000f 0x2a004ffff8000000

def z818 : W := mkw 0xbfff6db6b2004002 0x0afffdb6dac80100 0xfffffffee000000f 0xebfffffffb800000

def z819 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe0000831f 0xeefffffff800020c

def z820 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe00ff00fc2d 0x53fc0ff803fc03f0

def z821 : W := mkw 0x0254249600000000 0x0009509258000000 0x86d3fffe0000000f 0x6a1b4ffff8000000

def z822 : W := mkw 0xad03da09b709ed4f 0x42b40f6826dc27b5 0xff3ffe01ff1fffff 0xf7fcfff807fc7fff

def z823 : W := mkw 0x3da76db600000000 0x08f69db6d8000000 0xbfe3fffe0000000f 0xeaff8ffff8000000

def z824 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xb9fffffe0000000e 0x8ae7fffff8000000

def z825 : W := mkw 0x35a80000dad60030 0x04d6a000036b5800 0x79ec0001ffff0032 0xf5e7b00007fffc00

def z826 : W := mkw 0xc0009249b728ff0f 0x0300024926dca3fc 0x40000001ff00ff30 0x1100000007fc03fc

def z827 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe00040ccf 0xfafffffff8001033

def z828 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xff03fe00fc00fc3d 0xf3fc0ff803f003f0

def z829 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001ffff8ff3 0xf5fff00007fffe3f

def z830 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff00ff3f 0xfffc0ff807fc03fc

def z831 : W := mkw 0x58a3836961b9d749 0x41628e0da586e75d 0x79ff81f9e3fffff7 0xfde7fe07e78fffff

def z832 : W := mkw 0x3fff6db608440020 0x08fffdb6d8211000 0xbffffffe00e4000f 0xeefffffff8039000

def z833 : W := mkw 0x35a80000dad60030 0x04d6a000036b5800 0x7f2c0001ffff0031 0xf5fcb00007fffc00

def z834 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffdfffe0000000b 0x8afff7fff8000000

def z835 : W := mkw 0x18a3492000000000 0x00628d2480000000 0xb8e3fff80000000e 0xeae38fffe0000000

def z836 : W := mkw 0x08076db600000000 0x08201db6d8000000 0xb803fffe0000000c 0xeae00ffff8000000

def z837 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78f381f9e0fcf337 0xfde3ce07e783f3cc

def z838 : W := mkw 0x18a76db600000000 0x08629db6d8000000 0xb9fffffe0000000f 0xeae7fffff8000000

def z839 : W := mkw 0x0004861b2109c549 0x400012186c842715 0x413d8e3fe31fffff 0xbd04f638ff8c7fff

def z840 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfeffff800000006 0xeaffbfffe0000000

def z841 : W := mkw 0x35a80000d2920010 0x04d6a000034a4800 0x7fec0001fffb0033 0xf5ffb00007ffec00

def z842 : W := mkw 0xc00092492528ff0f 0x030002492494a3fc 0x000000000000ff00 0x00000000000003fc

def z843 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001ffff8c3f 0xf5fff00007fffe30

def z844 : W := mkw 0x675cecdf60b8d309 0x099d73b37d82e34c 0xc71c7e07e0f8f339 0x071c71f81f83e3cc

def z845 : W := mkw 0x400092496dfdffed 0xc100024925b7f7ff 0x40000001fffffff0 0x1500000007ffffff

def z846 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xfe03fe00fc007020 0x43f80ff803f001c0

def z847 : W := mkw 0x3fff6db608440020 0x08fffdb6d8211000 0xbffffffe1ce0002f 0xeafffffff8738000

def z848 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e201f9e0f8f332 0x4de38807e783e3cc

def z849 : W := mkw 0xad03da09b708ed0f 0x02b40f6826dc23b4 0xff03fe01ff18ff3d 0xf7fc0ff807fc63fc

def z850 : W := mkw 0x18a3016040b01200 0x00628c058102c048 0x78e381f9e0f8f336 0xede38e07e783e3cc

def z851 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f8fcd 0x9804f638fc0c7e3f

def z852 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7f3c0001ffff0031 0x95fcf00007fffc00

def z853 : W := mkw 0xad03db21b700ec0e 0x02b40f6c86dc03b0 0xff03fff9ff00fc3d 0xfbfc0fffe7fc03f0

def z854 : W := mkw 0xf5a09249f7b8ff0f 0x03d6824927dee3fc 0x7fe00001fff8ff33 0xf5ff800007ffe3fc

def z855 : W := mkw 0x58a3c96960b8d309 0x01628f25a582e34c 0xf8e3fff9e0f8f33e 0xefe38fffe783e3cc

def z856 : W := mkw 0x3fff6db6d2900000 0x08fffdb6db4a4000 0xfffffffffff8003f 0xffffffffffffe000

def z857 : W := mkw 0x3daf4d3200000000 0x08f6bd34c8000000 0xbfeffff80000000f 0xeaffbfffe0000000

def z858 : W := mkw 0x3da74d3200000000 0x00f69d34c8000000 0xbffffffe0000000f 0xeafffffff8000000

def z859 : W := mkw 0x3fff6db6d2920010 0x0cfffdb6db4a4800 0xfffffffee000000f 0xebfffffffb800000

def z860 : W := mkw 0x58a3016860b85301 0x01628c05a182e14c 0x78e381f8e0f87326 0xede38e07e383e1cc

def z861 : W := mkw 0xa75c7e969f442ca6 0x8a9d71fa5a7d10b2 0x871c7e061f040cc9 0x121c71f8187c1033

def z862 : W := mkw 0x1aff6db600000000 0x086bfdb6d8000000 0xb8fffffe0000000e 0xeae3fffff8000000

def z863 : W := mkw 0x12f0000048d40020 0x004bc00001235000 0x7ffc0001ffff0033 0xf5fff00007fffc00

def z864 : W := mkw 0x7fff6db660904000 0x09fffdb6d9824100 0xfffffffee000000f 0xebfffffffb800000

def z865 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xff03fe01ff00703d 0xf3fc0ff807fc01c0

def z866 : W := mkw 0x00009249dfffbffd 0xc4000249277ffeff 0x40000001fffffff0 0x1500000007ffffff

def z867 : W := mkw 0x18a76db600000000 0x08629db6d8000000 0x80e3fffe0000000e 0x0a038ffff8000000

def z868 : W := mkw 0x0004249600000000 0x0000109258000000 0x8003fffe0000000c 0x0a000ffff8000000

def z869 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86c271c61ce4fffc 0x5e1b09c7187393ff

def z870 : W := mkw 0x000414520c643aa4 0x80001051483190ea 0x013d8e3e1ce4ffff 0xbc04f638f87393ff

def z871 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xffc3ffc1ff00fc3f 0xfbff0fff07fc03f0

def z872 : W := mkw 0x275c7c969e4628b4 0x8c9d71f25a7918a2 0x871c7e061f070cc9 0x121c71f8187c1c33

def z873 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xfe03fe00fc00702c 0x43f80ff803f001c0

def z874 : W := mkw 0x2f5f6db69a460030 0x0cbd7db6da691800 0x871ffffe1f07000d 0x1a1c7ffff87c1c00

def z875 : W := mkw 0xad035a00b7006c06 0x02b40d6802dc01b0 0xff03fe00ff007c2d 0xf3fc0ff803fc01f0

def z876 : W := mkw 0x2d076db600000000 0x08b41db6d8000000 0xbe03fffe0000000c 0x4af80ffff8000000

def z877 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8003fff800000000 0x02000fffe0000000

def z878 : W := mkw 0x4807b7ff2529ffcd 0xc1201edffc94a7ff 0x8003fffe0000ffcc 0x0a000ffff80003ff

def z879 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbf3ffffe0000000d 0x8afcfffff8000000

def z880 : W := mkw 0x6f5b8169ba6ed339 0x05bd6e05a6e9bb4c 0x071f81f81f07f305 0x181c7e07e07c1fcc

def z881 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f87322 0xcde38e07e783e1cc

def z882 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xfe03fe01ff00fc3c 0x53f80ff807fc03f0

def z883 : W := mkw 0xc000924965b8ff0f 0x030002492596e3fc 0x40000001e0f8ff30 0x050000000783e3fc

def z884 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce0ffef 0x6a1b49c7187383ff

def z885 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff00fc0d 0x93fc0ff807fc03f0

def z886 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe00000002 0xcafffffff8000000

def z887 : W := mkw 0x3fff6db608440020 0x08fffdb6d8211000 0xbfffffff1fff003f 0xfefffffffc7ffc00

def z888 : W := mkw 0x000092490d6dbfed 0xc00002492435b6ff 0x000000001ce4fff0 0x14000000007393ff

def z889 : W := mkw 0xa5005a0097002c06 0x02940168025c00b0 0xff027e01ff00fc3d 0xf3fc09f807fc03f0

def z890 : W := mkw 0x2f576db600000000 0x08bd5db6d8000000 0xbfd3fffe0000000f 0xeaff4ffff8000000

def z891 : W := mkw 0x3fff6db608460030 0x0cfffdb6d8211800 0xbffffffe0007000f 0xeafffffff8001c00

def z892 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff23fe01ff18fc3f 0xf7fc8ff807fc63f0

def z893 : W := mkw 0xad03da01b701ec4e 0x42b40f6806dc07b1 0xff03fe01ff07fcfd 0xf3fc0ff807fc1ff3

def z894 : W := mkw 0x3daf6db600000000 0x08f6bdb6d8000000 0xb803fffe0000000c 0x0ae00ffff8000000

def z895 : W := mkw 0x3fff6db6d2920010 0x0cfffdb6db4a4800 0xffffffffe31f001f 0xffffffffff8c7c00

def z896 : W := mkw 0x18a76db600000000 0x08629db6d8000000 0xb8c3fffe0000000c 0x4ae30ffff8000000

def z897 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8023fffe0000000e 0xaa008ffff8000000

def z898 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78e381f9e0f87036 0xede38e07e783e1c0

def z899 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x7ee381f9fcf8f337 0xfdfb8e07e7f3e3cc

def z900 : W := mkw 0x52fc25fe48fe1331 0x0d4bf097f923f84c 0x00fc01fe00ff0302 0x0c03f007f803fc0c

def z901 : W := mkw 0x58a3836961b8d709 0x01628e0da586e35c 0x79e38ff9e3f8f336 0xede78e3fe78fe3cc

def z902 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7efc0001ffff0032 0x55fbf00007fffc00

def z903 : W := mkw 0x3fff6db640900000 0x08fffdb6d9024000 0xffffffffe3ff003f 0xffffffffff8ffc00

def z904 : W := mkw 0x2d076db600000000 0x08b41db6d8000000 0xb903fffe0000000c 0x8ae40ffff8000000

def z905 : W := mkw 0x58a3836961b9d749 0x41628e0da586e75d 0x79e38ff9e3ffffff 0xfde78e3fe78fffff

def z906 : W := mkw 0x480381692028d309 0x01200e05a480a34c 0x78c381f9e0e0f336 0xede30e07e78383cc

def z907 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe000403cf 0xeefffffff800100f

def z908 : W := mkw 0x37f89249dfffbffd 0xc4dfe249277ffeff 0x7ffc0001fffffff3 0xf5fff00007ffffff

def z909 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe00e0003f 0xeefffffff8038000

def z910 : W := mkw 0x3fff6db692000000 0x08fffdb6da480000 0xffffffffe300000f 0xebffffffff8c0000

def z911 : W := mkw 0x3fff6db6d2920010 0x0cfffdb6db4a4800 0xffffffffff1b003f 0xfbfffffffffc6c00

def z912 : W := mkw 0x80009249bf6dffef 0xc200024926fdb7ff 0x40000001fffffff0 0x1500000007ffffff

def z913 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xbffffffe1fff000f 0xfefffffff87ffc00

def z914 : W := mkw 0x2d076db600000000 0x08b41db6d8000000 0xbf3ffffe0000000f 0xeafcfffff8000000

def z915 : W := mkw 0x0803492000000000 0x00200d2480000000 0x8003fff80000000c 0x0a000fffe0000000

def z916 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013f8e3f031fffff 0xfc04fe38fc0c7fff

def z917 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x811ffffe0000000d 0x0a047ffff8000000

def z918 : W := mkw 0x0004861b01098549 0x400012186c042615 0x01fd8e3f03ff8fff 0xfc07f638fc0ffe3f

def z919 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x79ff81f9e0f8f337 0xede7fe07e783e3cc

def z920 : W := mkw 0xad03da09b708ed0f 0x02b40f6826dc23b4 0xff3ffe39ff1fff3f 0xfffcfff8e7fc7ffc

def z921 : W := mkw 0x2d076db692000000 0x08b41db6da480000 0xff03ffffff00003d 0xfbfc0ffffffc0000

def z922 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xffffffffe000003f 0xebffffffff800000

def z923 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff00fc2c 0xc3fc0ff807fc03f0

def z924 : W := mkw 0x0250a28d01098549 0x4009428a34042615 0x86d271c7031f8fdf 0x7e1b49c71c0c7e3f

def z925 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe00008fcf 0xeafffffff800023f

def z926 : W := mkw 0x52f425fe48fd13e1 0xc14bd097f923f44f 0x00fc01fe00ff03c2 0x0c03f007f803fc0f

def z927 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xffffffffff1f000f 0xfbfffffffffc7c00

def z928 : W := mkw 0x3fff6db648d60030 0x0cfffdb6d9235800 0xbffffffe1cff003f 0xfefffffff873fc00

def z929 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x79fc0001ffff0032 0x95e7f00007fffc00

def z930 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78f381ffe0fcf3f6 0xede3ce07ff83f3cf

def z931 : W := mkw 0x3fff6db69a460030 0x0cfffdb6da691800 0xbffffffe1c00000f 0xeafffffff8700000

def z932 : W := mkw 0xd8a3cb6961b8d70b 0x03628f2da586e35c 0x78e38ff9e0f8f336 0xede38e3fe783e3cc

def z933 : W := mkw 0x2f5f6db600000000 0x08bd7db6d8000000 0xbf1ffffe0000000d 0xeafc7ffff8000000

def z934 : W := mkw 0x0a5f6db600000000 0x08297db6d8000000 0x801ffffe0000000c 0x0a007ffff8000000

def z935 : W := mkw 0x3fff6db648d60030 0x0cfffdb6d9235800 0xbffffffe00e0000f 0xeafffffff8038000

def z936 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfffffff9ffff0033 0xf7ffffffe7fffc00

def z937 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff027e01ff00fc39 0x53fc09f807fc03f0

def z938 : W := mkw 0x10a00000dad60030 0x04428000036b5800 0x79fc0001ffff0033 0xf5e7f00007fffc00

def z939 : W := mkw 0x18a76db640900000 0x08629db6d9024000 0xf8e3ffffe0f8003e 0xefe38fffff83e000

def z940 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff00702d 0xe3fc0ff807fc01c0

def z941 : W := mkw 0xad03da09b708ed0f 0x02b40f6826dc23b4 0xff33fe3fff1cffff 0xfffccff8fffc73ff

def z942 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xfe03fe00fc00fc3d 0x73f80ff803f003f0

def z943 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f8f330 0xc5e38e07e783e3cc

def z944 : W := mkw 0x3fff6db692020010 0x0cfffdb6da480800 0xbffffffe0303000f 0xeafffffff80c0c00

def z945 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xffeffff9fffb0020 0xc3ffbfffe7ffec00

def z946 : W := mkw 0xc0009249f7b9ff4f 0x4300024927dee7fd 0x40000001fffffff0 0x1500000007ffffff

def z947 : W := mkw 0x18a381612020d208 0x00628e0584808348 0x78e381f9e0e0f336 0xede38e07e78383cc

def z948 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe07ff00fffd 0xfbfc0ff81ffc03ff

def z949 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffff800000003 0xe2ffffffe0000000

def z950 : W := mkw 0x58a3836961b8d709 0x01628e0da586e35c 0x78e38ff9e0f8ff3e 0xede38e3fe783e3fc

def z951 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff13fe01ff04fc3f 0xf7fc4ff807fc13f0

def z952 : W := mkw 0x35a80000dad60030 0x04d6a000036b5800 0x793c0001ffff0033 0xb5e4f00007fffc00

def z953 : W := mkw 0xad03da09b709ed4f 0x42b40f6826dc27b5 0xff03fe01ff1bfc3d 0xf3fc0ff807fc6ff0

def z954 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffd8039ffff0037 0xfdfff600e7fffc00

def z955 : W := mkw 0x58a3816960b9d349 0x41628e05a582e74d 0x78e381f9e0fff3f6 0xede38e07e783ffcf

def z956 : W := mkw 0x2f5f6db600000000 0x08bd7db6d8000000 0x8603fffe0000000c 0x0a180ffff8000000

def z957 : W := mkw 0x12f80000dad60030 0x044be000036b5800 0x78fc0001ffff0032 0xf5e3f00007fffc00

def z958 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7fec0001fffb0031 0xf1ffb00007ffec00

def z959 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfffffffefcff002f 0xeffffffffbf3fc00

def z960 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff3ffe01ff00fc3f 0xf3fcfff807fc03f0

def z961 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x87d3ffc61ce4ffff 0xfe1f4fff187393ff

def z962 : W := mkw 0x0004249600000000 0x0000109258000000 0x813ffffe0000000f 0xaa04fffff8000000

def z963 : W := mkw 0x12fc24de48ff13f1 0xc44bf0937923fc4f 0x00fc01fe00ff03c2 0x0c03f007f803fc0f

def z964 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe0000f03f 0xeafffffff80003c0

def z965 : W := mkw 0x3daf6db600000000 0x08f6bdb6d8000000 0xb92ffff800000000 0x82e4bfffe0000000

def z966 : W := mkw 0x58a3836961b9d749 0x41628e0da586e75d 0x78e381f9e3fbf336 0xede38e07e78fefcc

def z967 : W := mkw 0xa500da01b700ec0e 0x0294036806dc03b0 0xff007e01ff00fc39 0xf3fc01f807fc03f0

def z968 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86f271c71cfcffff 0xfe1bc9c71c73f3ff

def z969 : W := mkw 0xc807df7b2529ff4f 0x43201f7dec94a7fd 0x8003fffe0000ffcc 0x0a000ffff80003ff

def z970 : W := mkw 0xad035a00b7006c06 0x02b40d6802dc01b0 0xff027e00ff007020 0x43fc09f803fc01c0

def z971 : W := mkw 0x0004061a01090541 0x4000101868042415 0x013d8e3e031f0fcf 0xbc04f638f80c7c3f

def z972 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f8e0e0f326 0xe9e38e07e38383cc

def z973 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3e031f8fcf 0x1c04f638f80c7e3f

def z974 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8003fffe00008fcc 0x0a000ffff800023f

def z975 : W := mkw 0x3fff6db69a460030 0x0cfffdb6da691800 0xbfffffff1f1f001f 0xfefffffffc7c7c00

def z976 : W := mkw 0x37f82084dad60030 0x04dfe082136b5800 0xfffc7007ffff003b 0xf7fff1c01ffffc00

def z977 : W := mkw 0x58a3836961b8d709 0x01628e0da586e35c 0x79f38fffe3fcffff 0xfde7ce3fff8ff3ff

def z978 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78e201f8e0e07022 0x49e38807e38381c0

def z979 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff00fc30 0xd3fc0ff807fc03f0

def z980 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfffffffeffe7002f 0xfbfffffffbff9c00

def z981 : W := mkw 0x275000009a440020 0x009d400002691000 0x7ffc0001ffff0033 0xf5fff00007fffc00

def z982 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x87fe71c61ce4ffff 0xfe1ff9c7187393ff

def z983 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff1ffc3d 0xf7fc0ff807fc7ff0

def z984 : W := mkw 0x1aff6db600000000 0x086bfdb6d8000000 0x80c3fffe0000000c 0x0a030ffff8000000

def z985 : W := mkw 0x3fff6db648d60030 0x0cfffdb6d9235800 0xbfffffff03ff001f 0xfefffffffc0ffc00

def z986 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78c381f8e0e07020 0x41e30e07e38381c0

def z987 : W := mkw 0x58ab816960bad319 0x0562ae05a582eb4c 0x78ef81f9e0fbf336 0xede3be07e783efcc

def z988 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0001fffb0023 0xe1fff00007ffec00

def z989 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f87032 0xe5e38e07e783e1c0

def z990 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x87d271c71fe4ffff 0xfe1f49c71c7f93ff

def z991 : W := mkw 0x3daf6db600000000 0x08f6bdb6d8000000 0xb9effffe0000000e 0xeae7bffff8000000

def z992 : W := mkw 0x52fc25fe48fc13a1 0x894bf097f923f04e 0x00fc01fe00fc03c2 0x0c03f007f803f00f

def z993 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbec3fff800000000 0x42fb0fffe0000000

def z994 : W := mkw 0xad0bda01b702ec1e 0x06b42f6806dc0bb0 0xff0ffe01ff03fc3d 0xf3fc3ff807fc0ff0

def z995 : W := mkw 0x3fff6db69a440020 0x08fffdb6da691000 0xffffffffffe4003f 0xffffffffffff9000

def z996 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe0004001f 0xfefffffff8001000

def z997 : W := mkw 0x10a0804940b89309 0x004282012502e24c 0x78e381f9e0f8f336 0xede38e07e783e3cc

def z998 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381ffe0f8fffe 0xede38e07ff83e3ff

def z999 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff2ffe01ff1bfc3d 0xf3fcbff807fc6ff0

def z1000 : W := mkw 0x1aff6db648d60030 0x0c6bfdb6d9235800 0x80fffffe00ff000e 0x0e03fffff803fc00

def z1001 : W := mkw 0x1aff6db600000000 0x086bfdb6d8000000 0x86fffffe0000000f 0x6a1bfffff8000000

def z1002 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x79e38ff9e0f8f33f 0xede78e3fe783e3cc

def z1003 : W := mkw 0xad03d801b600e80e 0x02b40f6006d803a0 0xff03fe01fc00f03d 0xe3fc0ff807f003c0

def z1004 : W := mkw 0x58a3016860b85301 0x01628c05a182e14c 0x78e201f8e0f87020 0x41e38807e383e1c0

def z1005 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7fec0001fffb0032 0xe5ffb00007ffec00

def z1006 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe00fc00fc2d 0xe3fc0ff803f003f0

def z1007 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86f3f1fe1ce4ffff 0xfe1bcfc7f87393ff

def z1008 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff007031 0xf3fc0ff807fc01c0

def z1009 : W := mkw 0xc0009249fffcffaf 0x8300024927fff3fe 0x40000001fffcfff0 0x1500000007fff3ff

def z1010 : W := mkw 0xad035a00b7006c06 0x02b40d6802dc01b0 0xff027e01ff007c39 0xf3fc09f807fc01f0

def z1011 : W := mkw 0x35a80000dad60030 0x04d6a000036b5800 0x792c0001fffb0020 0x81e4b00007ffec00

def z1012 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfeffffe0000000c 0xcaffbffff8000000

def z1013 : W := mkw 0x2f5f6db600000000 0x08bd7db6d8000000 0x873ffffe0000000f 0xaa1cfffff8000000

def z1014 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8103fffe0000000d 0xaa040ffff8000000

def z1015 : W := mkw 0x1af76db600000000 0x086bddb6d8000000 0xbef3fffe0000000f 0xeafbcffff8000000

def z1016 : W := mkw 0x0254249608440020 0x0009509258211000 0x87ffffff1fff003f 0xfe1ffffffc7ffc00

def z1017 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e3fff336 0xfde38e07e78fffcc

def z1018 : W := mkw 0x18af6db600000000 0x0862bdb6d8000000 0x802ffffe0000000c 0x0a00bffff8000000

def z1019 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff00f034 0xe3fc0ff807fc03c0

def z1020 : W := mkw 0x025830c40c663ab4 0x840960c3103198ea 0x86de71c61ce7ffff 0x7e1b79c718739fff

def z1021 : W := mkw 0x2d03492000000000 0x00b40d2480000000 0xbf03fff80000000d 0xeafc0fffe0000000

def z1022 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0007ffff03f3 0xfdfff0001ffffc0f

def z1023 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff007c29 0xd3fc0ff807fc01f0

def z1024 : W := mkw 0x18a76db600000000 0x08629db6d8000000 0xb823fffe0000000c 0x8ae08ffff8000000

def z1025 : W := mkw 0x3fff6db6084400a0 0x88fffdb6d8211002 0xbffffffe000400cf 0xeafffffff8001003

def z1026 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe001f000f 0xeefffffff8007c00

def z1027 : W := mkw 0x25000000dad60030 0x04940000036b5800 0x7f3c0001ffff0033 0xf5fcf00007fffc00

def z1028 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f8f306 0x8de38e07e783e3cc

def z1029 : W := mkw 0x1aff6db600000000 0x086bfdb6d8000000 0x81fffffe0000000f 0xaa07fffff8000000

def z1030 : W := mkw 0x3fff6db608440020 0x08fffdb6d8211000 0xbffffffe1c04000f 0xfafffffff8701000

def z1031 : W := mkw 0x58a3836961b9d749 0x41628e0da586e75d 0x78e381f9e0f8fff6 0xede38e07e783e3ff

def z1032 : W := mkw 0x37f80120dad60030 0x04dfe004836b5800 0x7ffc01f9ffff0033 0xfdfff007e7fffc00

def z1033 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0xfffe7001ffff003f 0xf7fff9c007fffc00

def z1034 : W := mkw 0x3fff6db69a460030 0x0cfffdb6da691800 0xbffffffe1fe7003f 0xfefffffff87f9c00

def z1035 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfffffffefce4003f 0xfffffffffbf39000

def z1036 : W := mkw 0x58a3816160b0d208 0x01628e058582c348 0x78e381f9e0e0f036 0xe9e38e07e78383c0

def z1037 : W := mkw 0x3daf6db6d2920010 0x0cf6bdb6db4a4800 0xf92fffffe31b000c 0x8be4bfffff8c6c00

def z1038 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8013fffe00048fdf 0x3e004ffff800123f

def z1039 : W := mkw 0x58a3016860b85301 0x01628c05a182e14c 0x78e201f9e0f87332 0xede38807e783e1cc

def z1040 : W := mkw 0xad03da09b709ed4f 0x42b40f6826dc27b5 0xff23fe39ff1fffff 0xfffc8ff8e7fc7fff

def z1041 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbffffffe0307000f 0xfafffffff80c1c00

def z1042 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x813fffff031f001f 0xbe04fffffc0c7c00

def z1043 : W := mkw 0x37f82084dad60030 0x04dfe082136b5800 0xfffe71c1ffff0033 0xf7fff9c707fffc00

def z1044 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f8e0f8f326 0x4de38e07e383e3cc

def z1045 : W := mkw 0x27580000dad60030 0x049d6000036b5800 0x7f1c0001ffff0031 0xf5fc700007fffc00

def z1046 : W := mkw 0x2d076db600000000 0x08b41db6d8000000 0x8703fffe0000000d 0x0a1c0ffff8000000

def z1047 : W := mkw 0x3daf6db600000000 0x08f6bdb6d8000000 0xbf2ffffe0000000d 0xeafcbffff8000000

def z1048 : W := mkw 0x58a3836961b9d749 0x41628e0da586e75d 0x78f381ffe3ffffff 0xfde3ce07ff8fffff

def z1049 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f8f324 0xc9e38e07e783e3cc

def z1050 : W := mkw 0x0a576db600000000 0x08295db6d8000000 0x86c3fffe0000000c 0x4a1b0ffff8000000

def z1051 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbee3fffe0000000e 0xeafb8ffff8000000

def z1052 : W := mkw 0x3ffb69a400000000 0x08ffeda690000000 0xbfe3fff80000000f 0xeaff8fffe0000000

def z1053 : W := mkw 0x3fff6db69a460030 0x0cfffdb6da691800 0xffffffffff07003f 0xfbfffffffffc1c00

def z1054 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f8f034 0xe1e38e07e783e3c0

def z1055 : W := mkw 0x8807fedf2529ffcf 0xc2201ffb7c94a7ff 0x8003fffe0000ffcc 0x0a000ffff80003ff

def z1056 : W := mkw 0x3ff369a400000000 0x00ffcda690000000 0xbff3fffe0000000f 0xeaffcffff8000000

def z1057 : W := mkw 0xc0009249fffeff3f 0x0700024927fffbfc 0x40000001ffffff30 0x1500000007fffffc

def z1058 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff03fe01ff04fffd 0xf7fc0ff807fc13ff

def z1059 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff23fe39ff00fc3f 0xfbfc8ff8e7fc03f0

def z1060 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff1ffe01ff07fc3d 0xf3fc7ff807fc1ff0

def z1061 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x80c3fffe0000000e 0x6a030ffff8000000

def z1062 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xff027e00fc007029 0x43fc09f803f001c0

def z1063 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xfe03fe01fc00fc3c 0xe3f80ff807f003f0

def z1064 : W := mkw 0x080392012500ec0c 0x00200e48049403b0 0xff03fe01ff00fc3d 0xf3fc0ff807fc03f0

def z1065 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce4fff9 0x561b49c7187393ff

def z1066 : W := mkw 0x8803da012500ec0e 0x02200f68049403b0 0xfe03fe01fc00fc3d 0xf3f80ff807f003f0

def z1067 : W := mkw 0xf7f89249fffeff3f 0x07dfe24927fffbfc 0x7ffc0001ffffff33 0xf5fff00007fffffc

def z1068 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce4ffee 0x4e1b49c7187393ff

def z1069 : W := mkw 0x1af725b600000000 0x006bdc96d8000000 0xbffffffe0000000f 0xeafffffff8000000

def z1070 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfeffff80000000d 0xe2ffbfffe0000000

def z1071 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x8603fffe0000000d 0x6a180ffff8000000

def z1072 : W := mkw 0x3fff6db640900000 0x08fffdb6d9024000 0xbffffffe00f8000f 0xeefffffff803e000

def z1073 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfffffff031f8fdf 0xfefffffffc0c7e3f

def z1074 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0fcfff6 0xfde38e07e783f3ff

def z1075 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0xfee3f1f9e0f8f33f 0xeffb8fc7e783e3cc

def z1076 : W := mkw 0x000030c404203a84 0x800000c3101080ea 0x86c271c61ce0ffff 0x7e1b09c7187383ff

def z1077 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e181f9e0f8f332 0x8de38607e783e3cc

def z1078 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffc0007ffff0cfb 0xf5fff0001ffffc33

def z1079 : W := mkw 0x025092490d6dbfed 0xc00942492435b6ff 0x07fc00011ffffff3 0xf41ff000047fffff

def z1080 : W := mkw 0x3fff6db600010040 0x48fffdb6d8000401 0xbffffffe000700cf 0xeafffffff8001c03

def z1081 : W := mkw 0x50a0016840b81301 0x01428005a102e04c 0x78e201f9e0f8f336 0xede38807e783e3cc

def z1082 : W := mkw 0xad035a00b7006c06 0x02b40d6802dc01b0 0xff027e00ff00fc3d 0x73fc09f803fc03f0

def z1083 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfffffffffcf8003f 0xeffffffffff3e000

def z1084 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x78e381f9e0f87026 0xe9e38e07e783e1c0

def z1085 : W := mkw 0x58a3836961b8d709 0x01628e0da586e35c 0x78e381f9e3f8ff36 0xfde38e07e78fe3fc

def z1086 : W := mkw 0x0004861b01098549 0x400012186c042615 0x873ffe3f031f8fdf 0xfe1cfff8fc0c7e3f

def z1087 : W := mkw 0x3ffb492000000000 0x00ffed2480000000 0xbffffff80000000f 0xeaffffffe0000000

def z1088 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xff13fe07ff04fcfd 0xf3fc4ff81ffc13f3

def z1089 : W := mkw 0x000092490529bfcd 0xc00002492414a6ff 0x000000000000ffc0 0x00000000000003ff

def z1090 : W := mkw 0x0a576db600000000 0x08295db6d8000000 0x8613fffe0000000d 0x0a184ffff8000000

def z1091 : W := mkw 0x3fff6db692000000 0x08fffdb6da480000 0xbffffffe1f00000f 0xfafffffff87c0000

def z1092 : W := mkw 0x0a576db600000000 0x08295db6d8000000 0x87fffffe0000000f 0xea1ffffff8000000

def z1093 : W := mkw 0x025030c40c643aa4 0x800940c3103190ea 0x86d271c61ce4ffed 0x5a1b49c7187393ff

def z1094 : W := mkw 0x58a3016060b05200 0x01628c058182c148 0x78e381f8e0e07020 0xc1e38e07e38381c0

def z1095 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfffffff031b000f 0xeafffffffc0c6c00

def z1096 : W := mkw 0x3fff6db600000000 0x08fffdb6d8000000 0xbfc3fffe0000000d 0xeaff0ffff8000000

def z1097 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f8fd9 0x9404f638fc0c7e3f

def z1098 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f8fd2 0x9c04f638fc0c7e3f

def z1099 : W := mkw 0x58a3816960b8d309 0x01628e05a582e34c 0x79ef81f9e3fbf336 0xede7be07e78fefcc

def z1100 : W := mkw 0x37f80000dad60030 0x04dfe000036b5800 0x7ffd8e01ffff003f 0xf5fff63807fffc00

def z1101 : W := mkw 0x3fff6db640900000 0x08fffdb6d9024000 0xffffffffe018000f 0xebffffffff806000

def z1102 : W := mkw 0x0004861b01098549 0x400012186c042615 0x013d8e3f031f0fcb 0x9c04f638fc0c7c3f

def z1103 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xfec3fffefce0002c 0x4bfb0ffffbf38000

def z1104 : W := mkw 0x58a3016860b85301 0x01628c05a182e14c 0x78e201f8e0f8f336 0x6de38807e383e3cc

def z1105 : W := mkw 0xad035800b6006806 0x02b40d6002d801a0 0xff03fe00fc007020 0xc3fc0ff803f001c0

def z1106 : W := mkw 0x3fff6db6d2920010 0x0cfffdb6db4a4800 0xffffffffe3fb003f 0xefffffffff8fec00

def z1107 : W := mkw 0x3da34920d2900000 0x00f68d24834a4000 0xffe3fff9fff8003f 0xffff8fffe7ffe000

def z1108 : W := mkw 0x08076db600000000 0x08201db6d8000000 0x812ffffe0000000c 0x8a04bffff8000000

def z1109 : W := mkw 0xad03da01b700ec0e 0x02b40f6806dc03b0 0xffc3fe01ffe0fc3f 0xf7ff0ff807ff83f0

def z1110 : W := mkw 0x3fff6db6dad60030 0x0cfffdb6db6b5800 0xffffffffffe0003f 0xfbffffffffff8000

def z1111 : W := mkw 0x37f84800dad60030 0x04dfe120036b5800 0xfffc7e01ffff003b 0xf7fff1f807fffc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z8,z5,z9,z6]),(0,[z1,z10,z2,z3,z8,z5,z6]),(0,[z1,z11,z2,z3,z8,z5,z6]),(0,[z1,z2,z12,z3,z8,z5,z6]),(0,[z1,z2,z13,z3,z8,z5,z6])],[(0,[z14,z1,z2,z15,z3,z5,z6]),(0,[z16,z17,z2,z3,z8,z5,z6]),(0,[z18,z1,z2,z3,z8,z5,z6]),(0,[z19,z1,z2,z3,z8,z5,z6]),(0,[z20,z1,z21,z2,z3,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z6]),(0,[z1,z23,z2,z3,z8,z5,z6]),(0,[z24,z1,z2,z3,z8,z5,z6]),(0,[z1,z25,z2,z3,z8,z5,z6])],[(0,[z26,z20,z2,z3,z8,z5,z6]),(0,[z27,z1,z2,z3,z8,z5,z6]),(0,[z1,z21,z2,z3,z28,z5,z6]),(0,[z1,z2,z3,z8,z29,z5,z6]),(0,[z1,z2,z30,z3,z8,z5,z6])],[(0,[z31,z32,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z33,z6])],[(0,[z31,z2,z3,z8,z5,z6,z34]),(0,[z1,z2,z3,z8,z5,z35,z6]),(0,[z1,z36,z2,z3,z8,z37,z6]),(1,[z38,z1,z3,z8,z5,z39]),(0,[z1,z2,z40,z3,z8,z5,z6]),(0,[z1,z2,z41,z3,z8,z5,z6])],[(0,[z1,z2,z15,z42,z3,z5,z6]),(0,[z1,z2,z43,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z44,z6]),(0,[z1,z2,z3,z8,z5,z45,z6])]],
   [[(0,[z46,z1,z2,z15,z3,z5,z6]),(0,[z20,z1,z2,z3,z47,z5,z6])],[(0,[z48,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z49,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z3,z5,z6]),(0,[z1,z2,z15,z3,z50,z5,z6]),(0,[z1,z2,z3,z8,z5,z51,z6]),(0,[z1,z2,z52,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z53,z5,z6])],[(0,[z54,z1,z2,z3,z8,z5,z6]),(1,[z26,z2,z3,z47,z5,z6]),(0,[z32,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z56,z6]),(1,[z1,z2,z3,z5,z6,z57])],[(0,[z1,z2,z3,z8,z5,z33,z58]),(0,[z1,z2,z59,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z60]),(0,[z1,z2,z15,z3,z5,z61,z6]),(0,[z1,z2,z3,z8,z5,z6,z58])],[(0,[z14,z1,z2,z3,z62,z5,z6]),(1,[z1,z2,z3,z8,z5,z63]),(0,[z1,z2,z3,z8,z64,z5,z6])],[(0,[z1,z2,z3,z8,z65,z5,z6])],[(0,[z66,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z67,z1,z2,z3,z8,z5,z6]),(0,[z1,z68,z2,z3,z8,z5,z6]),(0,[z1,z2,z69,z3,z8,z5,z6]),(0,[z20,z1,z2,z3,z70,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z34])],[(0,[z14,z1,z2,z3,z8,z5,z71]),(0,[z1,z2,z72,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z73]),(0,[z74,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z75,z6]),(0,[z38,z1,z2,z3,z4,z5,z6]),(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z77,z6]),(0,[z1,z2,z3,z8,z78,z5,z79])],[(0,[z1,z2,z3,z8,z80,z5,z6])],[(1,[z1,z2,z3,z8,z81,z6]),(0,[z1,z2,z3,z8,z5,z81,z6]),(0,[z32,z1,z2,z3,z8,z5,z6]),(0,[z32,z2,z3,z8,z5,z33,z6]),(0,[z82,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z45,z6]),(0,[z1,z2,z15,z83,z3,z5,z6]),(0,[z84,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z85,z3,z5,z86])],[(0,[z1,z2,z87,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z88,z6])],[(0,[z1,z89,z2,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z90,z5,z6]),(0,[z91,z1,z2,z3,z8,z5,z6])],[(1,[z92,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z93,z6]),(0,[z1,z2,z3,z8,z5,z94,z6])]],
   [[(0,[z1,z95,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z96,z5,z6]),(0,[z97,z1,z21,z3,z8,z5,z6]),(0,[z1,z2,z98,z3,z8,z5,z6]),(0,[z1,z2,z15,z15,z3,z5,z6]),(0,[z99,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z100,z3,z5,z61,z6]),(0,[z1,z2,z101,z3,z8,z5,z6])],[(0,[z102,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z103,z3,z4,z5,z6])],[(0,[z104,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z105,z3,z8,z106,z6]),(0,[z1,z2,z3,z8,z107,z5,z6]),(0,[z1,z2,z108,z3,z8,z5,z6]),(0,[z1,z2,z109,z3,z8,z5,z6])],[(0,[z110,z1,z2,z3,z8,z5,z6]),(0,[z111,z1,z2,z3,z8,z5,z6]),(0,[z112,z1,z2,z3,z8,z5,z6]),(0,[z1,z21,z2,z15,z3,z5,z6]),(0,[z38,z1,z2,z3,z8,z5,z6]),(0,[z76,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z113])],[(0,[z1,z17,z3,z114,z8,z5,z6]),(1,[z110,z2,z115,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z116]),(0,[z1,z2,z3,z8,z5,z117,z6]),(0,[z1,z2,z85,z3,z5,z6,z86])],[(0,[z1,z2,z3,z8,z5,z118,z6]),(0,[z1,z2,z3,z4,z5,z6,z34]),(0,[z1,z2,z103,z8,z5,z119,z6])],[(0,[z1,z2,z120,z3,z8,z5,z6]),(0,[z121,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z100,z3,z8,z9,z6]),(0,[z122,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z123,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z5,z6,z57,z79])],[(0,[z1,z2,z124,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z125,z6]),(0,[z1,z2,z3,z8,z5,z6,z126]),(0,[z1,z2,z127,z8,z128,z5,z6]),(1,[z1,z2,z105,z3,z129,z6])]],
   [[(0,[z130,z1,z2,z3,z8,z5,z6]),(1,[z31,z2,z3,z8,z5,z34]),(0,[z1,z2,z3,z8,z5,z45,z34]),(0,[z1,z2,z3,z8,z5,z131,z6]),(0,[z132,z1,z2,z3,z8,z133,z6]),(0,[z1,z2,z83,z8,z5,z134,z6]),(0,[z1,z2,z3,z8,z5,z135,z6])],[(0,[z2,z3,z8,z106,z5,z9,z6]),(0,[z1,z2,z3,z8,z5,z6,z136]),(0,[z1,z2,z3,z8,z5,z137,z6]),(0,[z138,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z78,z5,z139])],[(1,[z1,z140,z3,z8,z5,z6]),(0,[z2,z3,z47,z8,z70,z5,z6]),(0,[z1,z2,z3,z8,z5,z141,z6]),(0,[z1,z2,z15,z85,z3,z5,z6]),(0,[z1,z2,z85,z3,z129,z5,z6]),(0,[z1,z2,z3,z8,z5,z142,z6])],[(0,[z1,z2,z3,z8,z5,z143,z6]),(0,[z1,z2,z3,z8,z144,z5,z6]),(0,[z1,z2,z3,z8,z5,z145,z6])],[(0,[z1,z2,z15,z3,z5,z6,z86]),(0,[z1,z2,z3,z8,z146,z5,z6]),(0,[z1,z2,z3,z147,z5,z6,z79]),(0,[z1,z2,z3,z8,z5,z148,z6])],[(0,[z20,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z78,z5,z6]),(0,[z1,z149,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z150,z6]),(0,[z151,z1,z2,z3,z8,z5,z6])],[(1,[z1,z2,z152,z8,z5,z6]),(0,[z1,z2,z3,z153,z8,z5,z6]),(0,[z1,z2,z154,z3,z8,z5,z142])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z155]),(0,[z156,z1,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z5,z33,z6,z34]),(0,[z1,z157,z2,z3,z4,z5,z6])],[(0,[z97,z1,z2,z3,z28,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z158])],[(0,[z1,z2,z3,z8,z5,z119,z33]),(0,[z1,z2,z3,z159,z8,z5,z6]),(0,[z1,z2,z15,z3,z129,z5,z6]),(0,[z1,z2,z154,z3,z5,z142,z6]),(0,[z1,z2,z3,z160,z8,z5,z6])],[(0,[z161,z1,z2,z3,z8,z5,z6]),(0,[z1,z162,z2,z3,z8,z5,z6])],[(0,[z1,z2,z163,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z164,z5,z6])],[(0,[z1,z2,z3,z8,z5,z165,z6]),(0,[z1,z2,z3,z8,z166,z5,z6]),(1,[z1,z2,z3,z167,z5,z6]),(0,[z168,z1,z2,z3,z8,z5,z6]),(0,[z169,z1,z2,z3,z8,z5,z6]),(0,[z170,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z34,z79]),(0,[z1,z2,z42,z3,z8,z5,z6]),(0,[z1,z2,z100,z85,z3,z5,z6]),(0,[z1,z2,z3,z8,z171,z5,z6])],[(0,[z172,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z173,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z142,z6])]],
   [[(1,[z1,z2,z3,z8,z5,z174]),(0,[z7,z1,z2,z3,z8,z5,z6]),(0,[z175,z1,z2,z3,z8,z9,z6]),(0,[z1,z2,z3,z8,z176,z5,z6]),(1,[z1,z21,z3,z177,z5,z6]),(0,[z1,z2,z3,z8,z5,z178,z6]),(0,[z132,z1,z36,z3,z8,z5,z6]),(0,[z179,z1,z2,z3,z8,z5,z6]),(0,[z180,z1,z2,z3,z8,z5,z6])],[(0,[z1,z181,z2,z3,z8,z5,z6]),(0,[z1,z2,z182,z3,z8,z5,z6]),(0,[z1,z36,z2,z3,z4,z5,z6]),(0,[z1,z157,z2,z3,z8,z5,z6]),(0,[z1,z2,z42,z3,z8,z5,z119]),(0,[z1,z2,z105,z3,z8,z61,z6])],[(0,[z1,z2,z3,z8,z62,z5,z6]),(0,[z1,z2,z183,z3,z8,z5,z6]),(1,[z1,z184,z3,z8,z5,z45])],[(0,[z1,z2,z3,z8,z5,z71,z6]),(0,[z1,z2,z185,z3,z8,z5,z6]),(0,[z1,z184,z2,z3,z4,z5,z6]),(0,[z186,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z187])],[(0,[z1,z2,z188,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z189,z6]),(0,[z1,z2,z3,z8,z190,z5,z6])],[(0,[z31,z1,z2,z3,z8,z5,z33]),(0,[z1,z2,z191,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z192]),(0,[z1,z89,z2,z193,z8,z5,z6]),(0,[z1,z2,z194,z3,z8,z5,z6])],[(0,[z1,z2,z195,z3,z8,z5,z6]),(0,[z1,z89,z3,z114,z8,z5,z6]),(0,[z1,z2,z103,z3,z8,z5,z58]),(0,[z1,z2,z196,z3,z8,z5,z6])]],
   [[(0,[z92,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z197,z4,z5,z6]),(0,[z26,z1,z2,z15,z3,z5,z6])],[(0,[z198,z1,z2,z3,z8,z5,z6]),(0,[z199,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z200,z5,z6]),(0,[z1,z193,z3,z114,z8,z5,z6]),(0,[z201,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z127,z3,z8,z128,z6]),(0,[z1,z202,z2,z3,z8,z5,z6])],[(0,[z1,z36,z2,z3,z8,z5,z6]),(0,[z1,z203,z2,z3,z8,z5,z6]),(0,[z204,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z205,z5,z6])],[(1,[z1,z2,z3,z206,z5,z6]),(0,[z110,z2,z115,z3,z8,z5,z6]),(0,[z207,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z208,z8,z5,z6]),(0,[z1,z2,z209,z3,z4,z5,z6]),(0,[z210,z1,z2,z3,z8,z5,z6])],[(0,[z46,z1,z2,z115,z8,z5,z6]),(0,[z211,z1,z2,z3,z8,z5,z6]),(0,[z1,z184,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z212,z8,z5,z6])],[(1,[z1,z2,z3,z8,z213,z6]),(0,[z1,z2,z85,z3,z8,z5,z34]),(0,[z1,z214,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z177,z5,z6]),(0,[z1,z2,z3,z215,z8,z5,z6]),(0,[z1,z2,z3,z8,z216,z5,z6])],[(0,[z1,z2,z3,z8,z5,z217,z6]),(0,[z1,z2,z218,z3,z8,z5,z6]),(0,[z219,z1,z2,z3,z8,z5,z6]),(0,[z1,z220,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z221,z8,z5,z6])],[(0,[z1,z2,z3,z8,z106,z133,z6]),(0,[z1,z2,z3,z8,z222,z5,z6]),(0,[z1,z36,z3,z8,z133,z5,z6]),(0,[z1,z223,z2,z3,z8,z5,z6])]],
   [[(0,[z224,z1,z2,z3,z8,z5,z6])],[(0,[z16,z1,z225,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z226]),(0,[z1,z2,z3,z197,z8,z5,z6]),(0,[z1,z2,z227,z3,z8,z5,z6]),(0,[z97,z1,z2,z15,z3,z5,z6]),(0,[z228,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z8,z4,z5,z6]),(0,[z1,z2,z3,z8,z229,z5,z6]),(0,[z1,z2,z230,z3,z8,z5,z6])],[(0,[z1,z2,z231,z3,z8,z5,z6]),(0,[z1,z2,z232,z3,z8,z5,z6]),(0,[z1,z2,z3,z114,z8,z5,z6])],[(0,[z1,z2,z233,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z234]),(0,[z1,z2,z3,z8,z235,z5,z6])],[(0,[z1,z2,z236,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z128,z9,z6]),(0,[z1,z2,z3,z237,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z238]),(0,[z1,z2,z209,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z239,z6]),(0,[z1,z2,z3,z8,z5,z6,z240])],[(0,[z1,z2,z3,z8,z5,z241,z6]),(0,[z175,z2,z3,z8,z106,z5,z6]),(0,[z242,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z243]),(0,[z1,z2,z244,z3,z8,z5,z6])],[(1,[z16,z17,z3,z8,z5,z6]),(0,[z1,z2,z3,z245,z8,z5,z6]),(0,[z1,z2,z3,z246,z8,z5,z6]),(0,[z1,z2,z247,z3,z8,z5,z6]),(0,[z1,z21,z3,z8,z177,z5,z6]),(0,[z248,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z147,z5,z6])],[(0,[z249,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z250,z6]),(0,[z1,z2,z15,z3,z5,z139,z6])]],
   [[(0,[z1,z251,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z252,z8,z5,z6]),(0,[z1,z2,z253,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z254,z6]),(0,[z1,z2,z154,z3,z8,z5,z86])],[(0,[z1,z2,z255,z3,z8,z5,z6]),(0,[z1,z256,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z257,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z258])],[(0,[z1,z259,z2,z3,z8,z5,z6]),(0,[z175,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z34,z58]),(0,[z260,z1,z2,z3,z8,z5,z6])],[(0,[z261,z1,z2,z3,z8,z5,z6]),(0,[z262,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z263,z8,z5,z6]),(0,[z97,z1,z3,z28,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z264,z6]),(0,[z1,z2,z3,z8,z5,z265,z6])],[(1,[z1,z2,z3,z8,z5,z266]),(0,[z1,z2,z15,z3,z197,z5,z6]),(0,[z267,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z164,z5,z6]),(0,[z1,z2,z3,z8,z5,z268,z6])],[(0,[z1,z269,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z270,z6]),(0,[z1,z2,z83,z3,z144,z5,z6])],[(0,[z1,z89,z2,z114,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z271,z6]),(0,[z1,z2,z15,z3,z128,z5,z6]),(0,[z1,z2,z272,z3,z8,z5,z6]),(0,[z1,z2,z273,z3,z8,z5,z6])]],
   [[(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z274,z8,z5,z6]),(0,[z1,z2,z275,z3,z8,z5,z6]),(0,[z276,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z277]),(0,[z1,z2,z3,z278,z8,z5,z6]),(0,[z1,z2,z3,z8,z279,z5,z6])],[(0,[z1,z17,z2,z3,z8,z5,z6]),(0,[z31,z1,z2,z15,z3,z5,z6]),(0,[z280,z1,z2,z3,z8,z5,z6]),(0,[z281,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z119,z6,z58]),(0,[z282,z1,z2,z3,z8,z5,z6]),(0,[z283,z1,z2,z3,z8,z5,z6])],[(0,[z26,z1,z2,z3,z8,z284,z6]),(0,[z1,z2,z3,z8,z5,z6,z285]),(0,[z1,z2,z15,z3,z5,z286,z6])],[(0,[z262,z1,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z287,z6]),(0,[z1,z2,z3,z8,z5,z287,z6]),(0,[z1,z2,z193,z197,z8,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z288,z8,z5,z6]),(0,[z1,z2,z154,z3,z8,z5,z33]),(1,[z1,z2,z289,z3,z5,z6])],[(0,[z1,z2,z3,z8,z290,z5,z6]),(0,[z1,z2,z3,z8,z5,z291,z6]),(0,[z1,z2,z3,z292,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z139,z6])],[(0,[z1,z2,z3,z293,z8,z5,z6]),(1,[z1,z2,z294,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z295]),(0,[z1,z2,z296,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z234]),(0,[z1,z2,z105,z3,z8,z9,z6]),(0,[z1,z2,z297,z3,z8,z5,z6]),(0,[z1,z2,z289,z127,z3,z5,z6])],[(0,[z14,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z298,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z45,z6,z39]),(0,[z1,z2,z3,z4,z5,z264,z6]),(0,[z1,z2,z127,z3,z8,z134,z6]),(0,[z1,z2,z3,z129,z5,z142,z6])],[(0,[z1,z2,z15,z105,z3,z5,z6])],[(1,[z1,z2,z3,z8,z299,z6]),(0,[z16,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z8,z5,z63]),(0,[z1,z2,z300,z3,z8,z5,z6]),(0,[z1,z2,z3,z301,z8,z5,z6]),(0,[z1,z2,z15,z3,z114,z5,z6]),(0,[z1,z2,z3,z8,z5,z302,z6]),(0,[z1,z2,z3,z8,z5,z303,z6]),(0,[z1,z2,z3,z8,z50,z5,z6]),(0,[z1,z2,z304,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z58])],[(0,[z1,z2,z3,z8,z5,z174,z6]),(0,[z1,z2,z15,z3,z106,z5,z6]),(0,[z1,z2,z305,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z64,z5,z6]),(0,[z1,z2,z306,z3,z8,z5,z6]),(0,[z1,z2,z307,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z308,z6]),(0,[z1,z2,z85,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z128,z5,z6]),(0,[z1,z2,z3,z8,z5,z61,z6]),(0,[z1,z2,z3,z8,z309,z5,z6])],[(0,[z46,z1,z2,z3,z8,z5,z6]),(1,[z1,z89,z114,z8,z5,z6]),(0,[z1,z310,z2,z3,z8,z5,z6])]],
   [[(1,[z46,z2,z197,z8,z5,z6]),(0,[z1,z2,z311,z3,z8,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z313,z5,z6])],[(0,[z1,z2,z3,z8,z5,z314,z6]),(0,[z1,z2,z315,z3,z8,z5,z6]),(0,[z1,z2,z3,z316,z8,z5,z6]),(1,[z1,z2,z317,z3,z8,z79])],[(0,[z1,z2,z3,z8,z5,z6,z266]),(0,[z318,z1,z2,z3,z8,z5,z6]),(0,[z319,z1,z2,z15,z3,z5,z6])],[(0,[z1,z2,z114,z197,z8,z5,z6]),(0,[z1,z2,z3,z8,z133,z9,z6]),(0,[z1,z2,z3,z320,z8,z5,z6])],[(0,[z16,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z321,z6]),(0,[z1,z2,z322,z3,z8,z5,z6]),(0,[z323,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z127,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z324,z5,z6])],[(0,[z325,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z326]),(0,[z1,z2,z3,z327,z8,z5,z6]),(0,[z97,z1,z2,z3,z177,z5,z6]),(0,[z1,z2,z15,z3,z4,z5,z6]),(0,[z1,z2,z328,z3,z8,z5,z6]),(0,[z1,z2,z100,z105,z3,z5,z6])],[(0,[z92,z1,z2,z225,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z329]),(0,[z1,z2,z85,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z42,z3,z4,z5,z6])],[(0,[z312,z1,z2,z3,z8,z5,z6]),(0,[z330,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z331]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z332,z3,z8,z5,z6]),(0,[z333,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z334,z3,z8,z5,z6])],[(1,[z1,z2,z3,z335,z5,z6]),(0,[z1,z2,z336,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z337]),(0,[z1,z2,z3,z4,z128,z5,z6]),(0,[z1,z2,z3,z4,z5,z61,z6]),(0,[z1,z2,z103,z3,z53,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z338]),(0,[z1,z2,z3,z8,z5,z339,z6]),(0,[z1,z2,z340,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z341,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z342]),(0,[z1,z2,z343,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z344,z6])],[(0,[z345,z1,z2,z3,z8,z5,z6]),(0,[z1,z89,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z346,z8,z5,z6])],[(0,[z46,z1,z347,z3,z8,z5,z6]),(0,[z1,z348,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z133,z5,z6]),(1,[z1,z2,z3,z53,z5,z6])],[(0,[z1,z2,z3,z8,z5,z139,z34]),(0,[z1,z2,z3,z28,z8,z5,z6]),(0,[z1,z2,z15,z3,z8,z5,z6]),(0,[z0,z1,z2,z15,z3,z5,z6]),(0,[z1,z349,z2,z3,z8,z5,z6]),(0,[z350,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z351,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z352,z3,z8,z5,z6]),(0,[z1,z2,z353,z3,z8,z5,z6]),(0,[z1,z2,z105,z3,z129,z5,z6])],[(0,[z1,z2,z354,z3,z8,z5,z6]),(0,[z1,z2,z355,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z356]),(0,[z357,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z100,z3,z4,z5,z6]),(0,[z1,z2,z358,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z359,z5,z6])],[(0,[z360,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z115,z114,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z33,z45]),(0,[z1,z2,z3,z8,z361,z5,z6]),(0,[z1,z2,z3,z362,z8,z5,z6]),(0,[z1,z2,z3,z8,z363,z5,z6]),(0,[z1,z2,z364,z15,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z365,z6]),(0,[z1,z2,z3,z8,z5,z366,z6])],[(0,[z14,z1,z2,z367,z8,z5,z6]),(0,[z1,z368,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z369,z5,z6]),(0,[z1,z2,z3,z370,z8,z5,z6]),(0,[z1,z371,z2,z3,z8,z5,z6])],[(0,[z1,z2,z15,z3,z5,z9,z6]),(0,[z1,z2,z3,z212,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z86])],[(0,[z1,z2,z372,z3,z8,z5,z6]),(0,[z373,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z100,z3,z5,z6]),(1,[z1,z2,z3,z80,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z374,z6]),(0,[z1,z2,z193,z3,z222,z5,z6]),(0,[z375,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z376,z3,z8,z5,z6])],[(0,[z14,z1,z225,z3,z8,z5,z6])],[(0,[z1,z2,z3,z377,z8,z5,z6]),(0,[z1,z2,z3,z8,z106,z37,z6]),(0,[z1,z2,z3,z8,z5,z6,z378])],[(0,[z1,z2,z3,z8,z5,z379,z6]),(0,[z1,z2,z3,z8,z5,z6,z326]),(0,[z380,z1,z2,z3,z8,z5,z6]),(1,[z20,z2,z3,z70,z5,z6]),(0,[z1,z2,z3,z8,z381,z5,z6]),(0,[z1,z2,z100,z3,z8,z5,z6]),(0,[z1,z2,z317,z3,z8,z78,z6])],[(0,[z1,z2,z382,z225,z3,z5,z6]),(0,[z46,z1,z2,z3,z383,z5,z6]),(0,[z1,z2,z3,z8,z5,z384,z6]),(0,[z1,z2,z3,z114,z4,z5,z6]),(0,[z132,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z129,z5,z6])],[(0,[z385,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z386,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z387,z5,z6]),(0,[z1,z2,z3,z8,z388,z5,z6]),(0,[z389,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z192,z6]),(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z1,z2,z3,z8,z78,z106,z6]),(0,[z1,z390,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z391]),(0,[z1,z2,z83,z3,z8,z128,z6])],[(0,[z1,z2,z3,z8,z5,z392,z6]),(0,[z1,z3,z8,z133,z5,z37,z6]),(0,[z1,z2,z393,z3,z8,z5,z6])]],
   [[(0,[z14,z2,z225,z3,z8,z5,z6]),(0,[z1,z2,z3,z47,z177,z5,z6]),(0,[z394,z1,z2,z3,z8,z5,z6]),(0,[z1,z395,z2,z3,z8,z5,z6])],[(0,[z396,z1,z2,z3,z8,z5,z6]),(0,[z1,z397,z2,z3,z8,z5,z6]),(0,[z1,z2,z398,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z399]),(0,[z1,z2,z3,z8,z5,z6,z400])],[(0,[z401,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z402,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z9,z37,z6]),(0,[z319,z1,z2,z193,z8,z5,z6]),(1,[z1,z2,z297,z3,z5,z6]),(0,[z1,z2,z317,z15,z3,z5,z6]),(0,[z1,z2,z83,z127,z8,z5,z6]),(0,[z1,z403,z2,z3,z8,z5,z6])],[(0,[z2,z115,z3,z197,z8,z5,z6]),(0,[z26,z1,z2,z3,z8,z5,z404]),(0,[z1,z2,z3,z405,z8,z5,z6]),(0,[z31,z1,z2,z3,z8,z406,z6]),(0,[z31,z1,z2,z3,z8,z407,z6]),(0,[z1,z21,z2,z3,z177,z5,z6]),(0,[z1,z2,z408,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z86]),(0,[z1,z2,z15,z3,z5,z409,z6])],[(0,[z1,z2,z225,z15,z3,z5,z6]),(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z410,z5,z6]),(0,[z1,z2,z3,z8,z5,z411,z6]),(0,[z412,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z5,z6,z39])],[(0,[z1,z2,z3,z8,z5,z9,z6]),(0,[z1,z2,z3,z8,z5,z413,z6]),(0,[z1,z2,z3,z8,z414,z5,z6]),(0,[z1,z2,z415,z15,z3,z5,z6])],[(0,[z319,z1,z17,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z416,z5,z6]),(0,[z1,z2,z42,z3,z8,z5,z58]),(0,[z1,z417,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z167,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z418,z6]),(1,[z76,z1,z2,z15,z5,z6]),(1,[z1,z2,z3,z144,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z419,z6]),(0,[z1,z2,z3,z8,z5,z6,z420]),(0,[z1,z2,z3,z8,z5,z421,z6]),(0,[z1,z2,z422,z3,z8,z5,z6]),(0,[z1,z2,z423,z3,z8,z5,z6]),(0,[z424,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z425,z5,z6]),(0,[z1,z2,z3,z8,z426,z5,z6]),(0,[z1,z184,z3,z8,z5,z45,z6]),(0,[z1,z2,z3,z427,z8,z5,z6])],[(0,[z1,z2,z3,z428,z8,z5,z6]),(0,[z1,z2,z3,z8,z429,z5,z6]),(0,[z1,z2,z3,z430,z8,z5,z6]),(0,[z1,z2,z431,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z129,z5,z6])],[(0,[z1,z21,z2,z432,z8,z5,z6]),(0,[z1,z2,z3,z8,z433,z5,z6]),(0,[z1,z2,z434,z3,z8,z5,z6]),(0,[z186,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z100,z3,z8,z129,z6]),(0,[z1,z2,z435,z3,z8,z5,z6])],[(0,[z14,z1,z2,z3,z8,z81,z6]),(0,[z1,z2,z3,z8,z5,z6,z436]),(1,[z1,z2,z15,z3,z5,z6])],[(0,[z1,z17,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z437]),(0,[z1,z2,z3,z28,z47,z5,z6]),(0,[z1,z2,z15,z3,z47,z5,z6]),(0,[z1,z2,z3,z8,z438,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z439]),(0,[z1,z440,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z441,z6]),(0,[z1,z2,z3,z442,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z443])],[(0,[z444,z1,z2,z3,z8,z5,z6]),(0,[z26,z2,z3,z47,z8,z5,z6]),(0,[z1,z2,z445,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z78,z139,z6])],[(0,[z1,z2,z446,z3,z8,z5,z6]),(0,[z447,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z448,z6]),(0,[z1,z2,z3,z8,z449,z5,z6])],[(0,[z26,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z450]),(0,[z1,z2,z3,z8,z5,z6,z451]),(0,[z1,z2,z3,z8,z177,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z5,z119,z6])]],
   [[(0,[z1,z2,z382,z3,z8,z5,z6]),(0,[z452,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z453,z3,z8,z5,z6]),(0,[z1,z2,z454,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z455,z6]),(1,[z1,z2,z127,z8,z128,z6]),(0,[z1,z2,z3,z5,z142,z6,z86])],[(0,[z1,z2,z3,z8,z5,z456,z6]),(0,[z1,z2,z3,z457,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z458,z6])],[(0,[z1,z2,z3,z4,z5,z9,z6]),(0,[z1,z2,z3,z8,z5,z6,z459]),(0,[z1,z2,z3,z8,z5,z409,z6]),(0,[z460,z1,z2,z3,z8,z5,z6])],[(0,[z7,z175,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z33,z39]),(0,[z1,z2,z3,z8,z5,z461,z6]),(0,[z1,z2,z3,z8,z5,z6,z39])],[(0,[z1,z2,z462,z3,z8,z5,z6]),(0,[z1,z2,z193,z115,z8,z5,z6]),(0,[z20,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z3,z28,z70,z5,z6]),(0,[z1,z2,z15,z3,z70,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z463]),(0,[z464,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z418,z6]),(0,[z1,z2,z8,z128,z5,z134,z6]),(0,[z1,z2,z3,z8,z465,z5,z6])],[(0,[z1,z2,z466,z3,z8,z5,z6]),(0,[z7,z1,z2,z3,z8,z106,z6]),(0,[z1,z2,z3,z467,z8,z5,z6])],[(1,[z1,z2,z3,z62,z5,z6]),(0,[z1,z2,z3,z8,z5,z468,z6])],[(0,[z469,z1,z2,z3,z8,z5,z6]),(0,[z319,z1,z89,z3,z8,z5,z6]),(0,[z1,z2,z3,z470,z8,z5,z6]),(0,[z38,z1,z2,z3,z8,z5,z45]),(0,[z1,z2,z306,z3,z4,z5,z6]),(0,[z1,z2,z83,z275,z3,z5,z6]),(0,[z1,z2,z471,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z472,z5,z6]),(0,[z1,z473,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z474,z5,z6]),(0,[z97,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z475,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z476,z6])],[(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z477,z6]),(0,[z1,z2,z3,z478,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z71]),(0,[z479,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z480,z3,z8,z5,z6]),(0,[z1,z2,z481,z3,z8,z5,z6])],[(0,[z1,z2,z3,z482,z8,z5,z6]),(0,[z1,z2,z3,z8,z383,z5,z6]),(0,[z1,z2,z3,z8,z483,z5,z6]),(0,[z319,z1,z2,z114,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z484,z6]),(0,[z485,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z486,z5,z6])],[(0,[z1,z225,z3,z114,z8,z5,z6]),(0,[z1,z2,z3,z4,z177,z5,z6]),(0,[z1,z2,z3,z8,z5,z487,z6])],[(0,[z1,z2,z488,z3,z8,z5,z6])],[(0,[z14,z1,z2,z152,z8,z5,z6]),(0,[z1,z2,z489,z3,z8,z5,z6]),(0,[z1,z490,z2,z3,z8,z5,z6]),(0,[z132,z1,z2,z3,z8,z37,z6]),(0,[z1,z2,z15,z3,z5,z37,z6]),(0,[z1,z2,z127,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z119,z6]),(0,[z1,z2,z3,z8,z5,z6,z491])],[(0,[z46,z1,z140,z3,z8,z5,z6]),(0,[z492,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z46,z1,z2,z3,z8,z493,z6]),(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z32,z1,z2,z3,z8,z5,z33]),(0,[z1,z2,z494,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z39]),(0,[z495,z1,z2,z15,z3,z5,z6]),(0,[z1,z203,z2,z15,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z496]),(0,[z1,z2,z497,z3,z8,z5,z6])],[(0,[z498,z1,z2,z3,z8,z5,z6]),(0,[z499,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z193,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z500,z6]),(0,[z1,z2,z289,z3,z8,z5,z6]),(0,[z501,z1,z2,z3,z8,z5,z6]),(0,[z502,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z70,z5,z6]),(1,[z1,z2,z3,z222,z5,z6]),(0,[z503,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z504,z5,z6]),(0,[z1,z2,z85,z3,z8,z5,z86])],[(0,[z1,z2,z3,z8,z505,z5,z6]),(0,[z1,z2,z3,z8,z106,z134,z6]),(0,[z506,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z507]),(1,[z1,z2,z386,z3,z5,z6]),(0,[z1,z2,z15,z3,z5,z33,z6]),(0,[z1,z2,z3,z8,z5,z286,z6])],[(1,[z1,z2,z3,z8,z284,z6]),(0,[z1,z2,z3,z8,z5,z284,z6]),(0,[z26,z1,z21,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z139,z6])],[(1,[z1,z2,z382,z3,z5,z6]),(0,[z1,z508,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z206,z8,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z6]),(0,[z1,z2,z509,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z510]),(0,[z1,z2,z3,z8,z5,z6,z511]),(0,[z1,z2,z3,z8,z5,z6,z57])]],
   [[(0,[z1,z2,z512,z3,z8,z5,z6]),(0,[z513,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z514,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z515]),(0,[z1,z2,z516,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z517,z5,z6])],[(0,[z518,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z47,z4,z5,z6]),(0,[z31,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z28,z4,z5,z6]),(0,[z1,z2,z83,z3,z8,z5,z6]),(1,[z1,z2,z100,z3,z61,z6])],[(1,[z175,z2,z3,z8,z106,z6]),(0,[z1,z2,z15,z3,z5,z6,z519])],[(0,[z1,z2,z3,z8,z5,z520,z6]),(0,[z24,z1,z2,z15,z3,z5,z6])],[(0,[z26,z1,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z8,z9,z134,z6]),(0,[z1,z21,z2,z3,z4,z5,z6]),(0,[z1,z2,z358,z3,z4,z5,z6]),(0,[z1,z2,z105,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z299,z5,z6]),(0,[z1,z2,z3,z177,z70,z5,z6]),(0,[z1,z2,z3,z8,z5,z37,z6]),(0,[z1,z2,z3,z521,z4,z5,z6])],[(0,[z1,z2,z115,z3,z483,z5,z6]),(0,[z1,z2,z3,z8,z5,z522,z6]),(0,[z1,z2,z3,z523,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z524,z6]),(0,[z1,z2,z40,z15,z3,z5,z6])],[(0,[z1,z2,z3,z8,z106,z5,z6]),(0,[z1,z2,z3,z525,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z526,z6])]],
   [[(0,[z1,z2,z3,z4,z70,z5,z6]),(0,[z1,z2,z3,z8,z5,z527,z6])],[(0,[z1,z528,z2,z3,z8,z5,z6]),(0,[z529,z1,z2,z3,z8,z5,z6])],[(0,[z530,z1,z2,z3,z8,z5,z6]),(0,[z531,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z47,z8,z5,z6]),(0,[z1,z2,z3,z147,z8,z5,z6]),(0,[z1,z2,z532,z3,z8,z5,z6])],[(0,[z533,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z534,z3,z8,z5,z6])],[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z26,z1,z2,z3,z70,z5,z6]),(0,[z1,z2,z3,z8,z5,z33,z6]),(0,[z1,z2,z3,z8,z5,z6,z535]),(0,[z1,z2,z100,z3,z8,z61,z6])],[(0,[z1,z21,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z5,z45,z6]),(0,[z1,z2,z105,z3,z8,z5,z6]),(0,[z1,z2,z536,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z537])],[(0,[z1,z2,z3,z521,z8,z5,z6]),(0,[z1,z2,z538,z3,z8,z5,z6]),(0,[z539,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z119,z34]),(0,[z1,z2,z193,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z540,z6]),(0,[z1,z2,z3,z8,z5,z6,z541]),(0,[z38,z1,z2,z3,z8,z5,z39]),(0,[z1,z2,z542,z3,z8,z5,z6])]],
   [[(0,[z46,z1,z2,z3,z206,z5,z6]),(0,[z1,z89,z2,z3,z167,z5,z6]),(0,[z1,z184,z2,z3,z8,z5,z45]),(0,[z1,z2,z543,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z6])],[(0,[z1,z2,z3,z544,z8,z5,z6]),(0,[z110,z1,z2,z197,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z545,z6]),(0,[z319,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z519])],[(0,[z76,z1,z2,z114,z8,z5,z6]),(0,[z1,z2,z546,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z37,z6]),(0,[z1,z2,z3,z8,z5,z547,z6])],[(0,[z1,z2,z2,z3,z8,z5,z6]),(0,[z138,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z548,z3,z8,z5,z6]),(1,[z1,z2,z114,z4,z5,z6]),(0,[z1,z2,z297,z193,z3,z5,z6]),(0,[z1,z2,z3,z432,z8,z5,z6]),(0,[z549,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z550,z8,z5,z6]),(0,[z551,z1,z2,z3,z8,z5,z6])],[(0,[z1,z552,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z483,z5,z6]),(0,[z1,z2,z3,z8,z213,z5,z6]),(0,[z1,z2,z3,z8,z78,z9,z6]),(0,[z553,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z106,z5,z6]),(1,[z1,z2,z3,z8,z406,z6]),(0,[z1,z2,z3,z8,z5,z406,z6]),(1,[z1,z2,z3,z8,z407,z6])],[(0,[z1,z2,z3,z8,z554,z5,z6]),(0,[z1,z2,z3,z8,z555,z5,z6]),(0,[z1,z2,z3,z8,z106,z6,z79]),(0,[z32,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z15,z3,z28,z5,z6])],[(0,[z1,z2,z15,z3,z5,z6,z34]),(0,[z1,z556,z2,z3,z8,z5,z6]),(1,[z319,z1,z193,z8,z5,z6]),(0,[z1,z21,z2,z546,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z557]),(0,[z1,z2,z3,z558,z8,z5,z6]),(0,[z1,z559,z2,z3,z8,z5,z6]),(0,[z1,z560,z2,z3,z8,z5,z6]),(0,[z561,z1,z2,z3,z8,z5,z6])],[(0,[z1,z562,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z563,z6]),(0,[z1,z2,z3,z8,z564,z5,z6]),(0,[z1,z2,z3,z8,z5,z565,z6]),(0,[z1,z2,z154,z85,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z566,z6])]],
   [[(0,[z1,z2,z3,z8,z567,z5,z6]),(0,[z1,z2,z3,z8,z133,z5,z6]),(0,[z1,z2,z154,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z5,z568,z6]),(0,[z1,z2,z543,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z569,z5,z6]),(0,[z570,z1,z2,z3,z8,z5,z6]),(0,[z31,z1,z2,z3,z8,z5,z34]),(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z571,z3,z8,z5,z6])],[(0,[z97,z26,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z128,z106,z6]),(0,[z572,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z154,z3,z5,z142])],[(0,[z14,z1,z2,z3,z8,z5,z266]),(0,[z110,z1,z2,z15,z3,z5,z6]),(0,[z1,z573,z2,z3,z8,z5,z6]),(0,[z1,z2,z574,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z575]),(0,[z38,z1,z2,z15,z3,z5,z6]),(0,[z76,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z105,z3,z8,z129,z6]),(0,[z1,z2,z3,z8,z5,z6,z576])],[(0,[z1,z2,z3,z8,z9,z6,z79]),(0,[z132,z1,z3,z8,z5,z37,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z1,z2,z578,z3,z8,z5,z6]),(0,[z1,z2,z85,z3,z8,z5,z142])],[(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z579,z6])],[(0,[z580,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z3,z78,z5,z6])]],
   [[(0,[z1,z581,z2,z3,z8,z5,z6]),(0,[z1,z2,z582,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z583]),(0,[z1,z2,z15,z3,z5,z134,z6]),(0,[z1,z2,z3,z8,z5,z6,z584])],[(0,[z26,z1,z2,z3,z4,z5,z6]),(1,[z32,z2,z3,z8,z5,z33]),(0,[z1,z2,z585,z3,z8,z5,z6]),(0,[z586,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z587,z6]),(0,[z1,z2,z154,z3,z8,z5,z6])],[(0,[z16,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z347,z3,z8,z5,z6]),(0,[z1,z2,z364,z3,z8,z5,z6]),(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z36,z2,z3,z8,z133,z6]),(0,[z1,z2,z588,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z589,z6])],[(0,[z1,z2,z3,z8,z5,z590,z6]),(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z76,z1,z2,z543,z8,z5,z6]),(0,[z1,z2,z103,z591,z3,z5,z6]),(0,[z1,z2,z3,z592,z8,z5,z6])],[(0,[z1,z2,z593,z3,z8,z5,z6]),(0,[z1,z2,z3,z594,z8,z5,z6]),(0,[z595,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z193,z8,z4,z5,z6]),(1,[z1,z2,z543,z4,z5,z6]),(0,[z596,z1,z2,z3,z8,z5,z6]),(0,[z1,z597,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z598,z5,z6])],[(0,[z1,z2,z599,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z600,z5,z6]),(0,[z1,z2,z3,z4,z133,z5,z6]),(0,[z1,z2,z3,z4,z567,z5,z6]),(0,[z1,z2,z601,z3,z8,z5,z6]),(0,[z602,z1,z2,z3,z8,z5,z6])],[(0,[z1,z3,z28,z8,z177,z5,z6]),(0,[z603,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z577,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z604,z5,z6]),(1,[z1,z2,z591,z3,z5,z6])],[(0,[z1,z2,z3,z605,z8,z5,z6]),(1,[z1,z36,z3,z8,z133,z6]),(0,[z1,z2,z3,z8,z5,z6,z606])]],
   [[(0,[z1,z2,z607,z3,z8,z5,z6]),(0,[z1,z2,z317,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z5,z142,z6]),(1,[z1,z2,z275,z3,z5,z6]),(0,[z1,z2,z608,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z63,z6]),(0,[z1,z2,z3,z8,z5,z34,z39]),(0,[z1,z2,z609,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z610,z5,z6])],[(0,[z14,z1,z2,z3,z8,z299,z6]),(0,[z1,z2,z225,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z8,z287,z6]),(0,[z611,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z193,z3,z5,z6]),(0,[z612,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z294,z42,z3,z5,z6]),(0,[z1,z2,z317,z3,z8,z5,z79])],[(0,[z7,z1,z2,z3,z8,z9,z6]),(0,[z132,z1,z2,z3,z8,z5,z6]),(0,[z201,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z115,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z493,z5,z6]),(0,[z1,z2,z3,z8,z5,z613,z6]),(0,[z7,z1,z2,z3,z8,z5,z234]),(0,[z1,z614,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z615])],[(0,[z1,z2,z3,z8,z616,z5,z6]),(0,[z1,z2,z3,z8,z617,z5,z6]),(0,[z1,z2,z618,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z404]),(0,[z619,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z543,z8,z4,z5,z6]),(0,[z1,z2,z15,z620,z3,z5,z6]),(0,[z1,z2,z621,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z78,z5,z6])],[(0,[z1,z2,z3,z8,z622,z5,z6]),(0,[z1,z2,z3,z8,z5,z134,z6]),(0,[z1,z2,z3,z8,z623,z5,z6])]],
   [[(0,[z1,z2,z624,z3,z8,z5,z6]),(0,[z625,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z626,z3,z8,z5,z6]),(0,[z1,z184,z2,z3,z8,z5,z39]),(0,[z1,z2,z620,z3,z8,z5,z6]),(0,[z1,z2,z3,z129,z5,z61,z6]),(0,[z1,z2,z627,z3,z8,z5,z6])],[(0,[z319,z1,z225,z3,z8,z5,z6]),(0,[z1,z2,z3,z628,z8,z5,z6]),(0,[z7,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z629,z3,z8,z5,z6]),(0,[z1,z2,z3,z630,z8,z5,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z631,z3,z8,z5,z6]),(0,[z1,z2,z317,z3,z8,z5,z6]),(0,[z632,z1,z2,z3,z8,z5,z6])],[(0,[z633,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z634,z3,z8,z5,z6]),(0,[z20,z2,z3,z8,z70,z5,z6]),(0,[z1,z2,z3,z635,z8,z5,z6]),(0,[z1,z2,z114,z8,z4,z5,z6]),(0,[z1,z2,z3,z8,z636,z5,z6]),(0,[z1,z2,z42,z8,z5,z6,z58])],[(0,[z1,z2,z225,z3,z8,z5,z6])],[(0,[z1,z2,z415,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z637,z5,z6]),(0,[z1,z2,z103,z42,z8,z5,z6]),(0,[z1,z2,z42,z3,z164,z5,z6]),(0,[z1,z2,z3,z8,z5,z638,z6]),(0,[z1,z2,z100,z3,z5,z142,z6])],[(0,[z26,z1,z2,z3,z8,z5,z174]),(0,[z639,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z640,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z641]),(0,[z1,z2,z3,z8,z139,z6,z79])],[],[(0,[z642,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z643,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z644,z6]),(0,[z1,z2,z645,z3,z8,z5,z6]),(0,[z1,z2,z646,z3,z8,z5,z6]),(0,[z1,z2,z103,z3,z8,z5,z6])]],
   [[(1,[z1,z2,z3,z8,z493,z6]),(0,[z1,z2,z100,z3,z8,z106,z6]),(0,[z1,z2,z3,z8,z5,z647,z6]),(0,[z1,z2,z648,z3,z8,z5,z6]),(0,[z649,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z650,z3,z8,z5,z6]),(0,[z1,z2,z195,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z651,z6])],[(0,[z1,z2,z15,z3,z5,z6,z79]),(0,[z1,z2,z83,z3,z8,z134,z6]),(0,[z1,z2,z317,z3,z8,z5,z139])],[(1,[z1,z2,z3,z8,z5,z6]),(0,[z14,z1,z2,z3,z335,z5,z6]),(0,[z1,z2,z652,z3,z8,z5,z6]),(0,[z1,z2,z653,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z1,z2,z154,z3,z8,z5,z34]),(0,[z1,z2,z3,z8,z5,z139,z33]),(0,[z1,z2,z3,z8,z5,z654,z6]),(0,[z1,z2,z15,z127,z3,z5,z6]),(1,[z1,z2,z83,z8,z134,z6]),(0,[z1,z2,z103,z3,z8,z5,z119])],[(0,[z14,z1,z17,z3,z8,z5,z6]),(0,[z1,z2,z367,z3,z8,z5,z6]),(0,[z46,z1,z2,z3,z8,z5,z326]),(0,[z1,z2,z3,z8,z5,z655,z6]),(0,[z1,z36,z2,z15,z3,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z656,z5,z6]),(0,[z76,z1,z2,z193,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z134,z6]),(0,[z1,z2,z3,z4,z622,z5,z6]),(0,[z1,z2,z15,z601,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z657,z6])],[(1,[z7,z2,z3,z8,z9,z6]),(0,[z1,z184,z2,z15,z3,z5,z6])],[(0,[z658,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z15,z115,z3,z5,z6]),(0,[z1,z89,z2,z3,z96,z5,z6]),(0,[z659,z1,z2,z3,z8,z5,z6])],[(0,[z76,z1,z2,z15,z8,z5,z6]),(0,[z1,z2,z317,z3,z8,z6,z79])]],
   [[(0,[z1,z2,z3,z152,z8,z5,z6]),(0,[z97,z20,z1,z2,z3,z5,z6]),(1,[z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z8,z660,z5,z6])],[(0,[z1,z2,z3,z8,z5,z661,z6]),(0,[z1,z2,z3,z8,z5,z6,z662])],[(0,[z1,z2,z3,z335,z8,z5,z6]),(0,[z26,z1,z2,z3,z8,z213,z6]),(0,[z32,z1,z2,z3,z8,z5,z34]),(0,[z1,z2,z3,z8,z5,z663,z6]),(0,[z1,z2,z3,z664,z8,z5,z6])],[(1,[z14,z225,z3,z8,z5,z6]),(0,[z20,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z404]),(1,[z1,z2,z546,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z665,z6])],[(0,[z46,z2,z3,z197,z8,z5,z6]),(0,[z1,z2,z666,z3,z8,z5,z6]),(0,[z1,z2,z667,z3,z8,z5,z6])],[],[(0,[z16,z1,z17,z3,z8,z5,z6]),(0,[z1,z2,z668,z3,z8,z5,z6]),(0,[z1,z2,z669,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z119,z6])],[(0,[z670,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z671,z5,z6]),(0,[z1,z2,z672,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z673]),(0,[z38,z1,z184,z3,z8,z5,z6]),(0,[z1,z2,z674,z3,z8,z5,z6])]],
   [[(0,[z14,z16,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z33,z79]),(0,[z1,z2,z15,z103,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z79]),(0,[z1,z2,z3,z8,z5,z6,z675])],[(1,[z1,z347,z3,z8,z5,z6]),(0,[z676,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z677,z5,z6]),(0,[z1,z678,z2,z3,z8,z5,z6]),(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z679,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z680,z3,z8,z5,z6])],[(0,[z175,z1,z2,z3,z8,z106,z6]),(0,[z1,z2,z15,z154,z3,z5,z6])],[(0,[z175,z1,z2,z15,z3,z5,z6]),(0,[z1,z2,z85,z3,z8,z5,z33]),(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z681,z3,z8,z5,z6]),(1,[z132,z1,z3,z8,z37,z6]),(0,[z38,z1,z3,z8,z5,z6,z39])],[(0,[z1,z2,z386,z115,z3,z5,z6]),(1,[z1,z2,z42,z8,z5,z58]),(0,[z1,z682,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z683])],[(0,[z1,z2,z3,z8,z684,z5,z6]),(0,[z1,z140,z2,z3,z8,z5,z6]),(0,[z1,z2,z685,z3,z8,z5,z6]),(0,[z1,z2,z686,z3,z8,z5,z6]),(0,[z1,z2,z687,z3,z8,z5,z6]),(0,[z1,z2,z688,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z689,z5,z6])],[(0,[z46,z1,z2,z3,z8,z5,z192]),(0,[z1,z690,z2,z3,z8,z5,z6])],[(0,[z1,z2,z691,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z6]),(0,[z1,z2,z3,z8,z96,z5,z6]),(0,[z495,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z692,z6])]],
   [[(0,[z110,z1,z2,z115,z8,z5,z6]),(0,[z319,z1,z193,z3,z8,z5,z6]),(0,[z1,z2,z693,z3,z8,z5,z6]),(0,[z1,z2,z694,z3,z8,z5,z6]),(0,[z1,z2,z294,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z407,z5,z6]),(0,[z1,z2,z3,z8,z5,z695,z6]),(0,[z1,z2,z127,z3,z80,z5,z6])],[(1,[z1,z2,z432,z8,z5,z6]),(0,[z1,z2,z591,z3,z8,z5,z6]),(0,[z1,z2,z696,z3,z8,z5,z6])],[(0,[z1,z17,z2,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z697]),(0,[z1,z2,z698,z3,z8,z5,z6]),(0,[z699,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z700,z3,z8,z5,z6])],[(0,[z1,z2,z701,z3,z8,z5,z6]),(0,[z1,z2,z702,z3,z8,z5,z6]),(0,[z1,z2,z15,z543,z3,z5,z6])],[(0,[z17,z2,z225,z3,z8,z5,z6]),(0,[z1,z2,z3,z703,z8,z5,z6]),(0,[z46,z1,z2,z197,z8,z5,z6]),(0,[z704,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z79]),(0,[z1,z2,z15,z3,z5,z6,z58]),(0,[z1,z705,z2,z3,z8,z5,z6])],[(1,[z1,z2,z367,z8,z5,z6])],[(0,[z46,z110,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z383,z5,z6]),(0,[z1,z2,z3,z8,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z287,z326]),(0,[z170,z2,z3,z8,z5,z34]),(0,[z1,z2,z3,z707,z5,z6]),(1,[z1,z2,z708,z5,z6]),(0,[z1,z2,z83,z4,z134,z6]),(0,[z1,z2,z3,z709,z5,z6])],[(0,[z14,z225,z3,z8,z81,z6]),(0,[z1,z2,z3,z8,z5,z710]),(0,[z711,z2,z3,z8,z5,z6])],[(0,[z1,z2,z152,z62,z5,z6]),(0,[z1,z2,z712,z8,z5,z6]),(0,[z1,z184,z15,z3,z5,z45]),(0,[z1,z2,z15,z708,z5,z6])],[(0,[z7,z2,z3,z4,z9,z6]),(0,[z713,z1,z3,z8,z5,z6]),(0,[z1,z2,z714,z4,z5,z6]),(0,[z1,z2,z3,z8,z715,z6]),(0,[z1,z2,z105,z3,z129,z6])],[(0,[z31,z2,z3,z8,z5,z34])],[(0,[z1,z2,z3,z716,z5,z6]),(0,[z717,z2,z3,z8,z5,z6]),(0,[z718,z2,z3,z8,z5,z6])],[(0,[z1,z140,z3,z8,z5,z6]),(0,[z1,z2,z152,z8,z5,z71]),(0,[z1,z2,z719,z8,z5,z6]),(0,[z1,z2,z3,z720,z5,z6]),(0,[z1,z2,z15,z3,z5,z192]),(0,[z2,z3,z47,z721,z5,z6]),(0,[z561,z2,z3,z8,z9,z6])],[(0,[z1,z2,z3,z335,z5,z71]),(0,[z1,z2,z3,z8,z493,z6]),(0,[z1,z2,z3,z8,z5,z722])]],
   [[(0,[z2,z723,z197,z8,z5,z6]),(0,[z110,z2,z15,z115,z5,z6]),(0,[z1,z2,z3,z721,z5,z6]),(0,[z1,z2,z193,z96,z5,z6]),(0,[z1,z2,z3,z8,z5,z724]),(0,[z1,z2,z725,z8,z5,z6])],[(0,[z14,z225,z3,z4,z5,z6]),(0,[z1,z2,z3,z726,z5,z6]),(0,[z611,z2,z115,z8,z5,z6]),(0,[z32,z2,z3,z8,z5,z727]),(0,[z1,z728,z114,z8,z5,z6]),(0,[z1,z2,z546,z4,z5,z6]),(0,[z1,z2,z3,z729,z5,z6]),(0,[z1,z2,z127,z80,z128,z6])],[(0,[z1,z2,z434,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z2,z3,z8,z5,z731])],[(0,[z1,z2,z152,z732,z5,z6]),(0,[z1,z2,z3,z335,z299,z6]),(0,[z1,z2,z3,z733,z5,z6]),(0,[z46,z2,z197,z8,z5,z326]),(0,[z1,z2,z523,z4,z5,z6]),(0,[z1,z2,z734,z3,z8,z5])],[(0,[z1,z2,z3,z8,z735,z6]),(0,[z26,z2,z3,z521,z5,z6]),(0,[z2,z3,z8,z106,z736,z6]),(0,[z1,z89,z728,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z737])],[(0,[z1,z2,z738,z3,z8,z5]),(0,[z1,z2,z15,z3,z213,z6]),(0,[z1,z2,z3,z8,z9,z234]),(0,[z24,z2,z195,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z739]),(0,[z1,z2,z8,z5,z740,z6])],[(0,[z1,z347,z3,z4,z5,z6]),(0,[z741,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z147,z9,z6]),(0,[z1,z2,z4,z5,z647,z6]),(0,[z1,z742,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z743,z6])],[(0,[z1,z2,z744,z8,z5,z6]),(0,[z1,z2,z3,z8,z736,z6]),(0,[z1,z2,z3,z167,z5,z6]),(0,[z132,z1,z3,z4,z37,z6]),(0,[z1,z2,z306,z3,z5,z86])],[(0,[z1,z2,z3,z745,z5,z6]),(0,[z1,z2,z746,z3,z5,z6]),(0,[z2,z3,z747,z8,z5,z6]),(0,[z1,z2,z15,z362,z5,z6]),(0,[z1,z2,z42,z4,z5,z58])],[(0,[z1,z2,z3,z8,z5,z730]),(0,[z20,z1,z2,z432,z5,z6]),(0,[z1,z2,z15,z3,z5,z234]),(0,[z1,z2,z3,z748,z5,z6]),(0,[z1,z2,z749,z3,z4,z5]),(0,[z1,z2,z209,z3,z418,z6])],[(0,[z14,z225,z152,z8,z5,z6]),(0,[z1,z2,z367,z8,z81,z6]),(0,[z1,z2,z3,z8,z750,z6]),(0,[z1,z2,z3,z8,z5,z174]),(0,[z1,z2,z3,z751,z5,z6]),(0,[z1,z2,z3,z8,z752,z6])],[(0,[z1,z21,z69,z3,z5,z6]),(0,[z1,z2,z15,z478,z5,z6])],[(0,[z1,z347,z3,z8,z493,z6]),(0,[z1,z2,z3,z753,z5,z6]),(0,[z754,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z755,z5,z6])],[(0,[z1,z2,z3,z756,z5,z6]),(0,[z1,z2,z757,z8,z5,z6]),(0,[z1,z157,z3,z177,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z758]),(0,[z1,z347,z3,z8,z5,z6]),(0,[z1,z2,z432,z4,z5,z6]),(0,[z1,z2,z550,z4,z5,z6])],[(0,[z501,z2,z3,z8,z5,z34]),(0,[z1,z163,z114,z8,z5,z6]),(0,[z1,z2,z759,z8,z5,z6])],[(0,[z1,z2,z3,z760,z5,z6]),(0,[z132,z1,z3,z8,z37,z6])],[(0,[z1,z761,z3,z8,z5,z6]),(0,[z1,z2,z762,z8,z5,z6]),(0,[z1,z2,z42,z8,z5,z58])],[(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z2,z196,z4,z5,z6])],[(0,[z110,z2,z115,z483,z5,z6]),(0,[z1,z3,z8,z5,z6,z764]),(0,[z2,z3,z8,z5,z727,z34]),(0,[z1,z2,z183,z4,z5,z6])],[],[(0,[z1,z2,z3,z206,z5,z6]),(0,[z1,z2,z3,z4,z765,z6]),(0,[z1,z2,z3,z8,z6,z731])]],
   [[(0,[z1,z2,z766,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z767]),(0,[z76,z1,z2,z297,z5,z6])],[(0,[z1,z2,z768,z3,z8,z6]),(0,[z1,z2,z3,z8,z769,z6]),(0,[z1,z2,z3,z8,z5,z770]),(0,[z1,z2,z3,z8,z5,z740])],[(0,[z1,z2,z3,z8,z771,z6]),(0,[z110,z2,z386,z115,z5,z6]),(0,[z1,z157,z114,z4,z5,z6])],[(0,[z1,z140,z3,z383,z5,z6]),(0,[z38,z1,z3,z4,z5,z39]),(0,[z1,z2,z8,z5,z740,z58])],[(0,[z1,z2,z772,z8,z5,z6]),(0,[z1,z2,z773,z3,z8,z6]),(0,[z1,z2,z3,z383,z493,z6]),(0,[z1,z2,z3,z774,z5,z6])],[(0,[z1,z2,z3,z775,z5,z6])],[(0,[z26,z2,z3,z47,z5,z404]),(0,[z1,z3,z8,z133,z769,z6]),(0,[z1,z2,z15,z3,z776,z6]),(0,[z1,z2,z15,z467,z5,z6]),(0,[z1,z777,z3,z8,z5,z6]),(0,[z1,z2,z154,z3,z5,z778])],[(0,[z1,z2,z15,z3,z5,z71]),(0,[z1,z779,z3,z8,z5,z6]),(0,[z1,z728,z3,z8,z5,z6]),(0,[z1,z2,z780,z3,z5,z6]),(0,[z1,z2,z15,z83,z134,z6])]],
   [[(0,[z1,z2,z3,z8,z781,z6]),(0,[z1,z2,z782,z3,z8,z5]),(0,[z1,z2,z4,z5,z6,z537]),(0,[z1,z2,z3,z8,z765,z6])],[],[(0,[z16,z17,z3,z8,z5,z6]),(0,[z1,z2,z3,z783,z5,z6]),(0,[z207,z2,z197,z8,z5,z6]),(0,[z1,z784,z3,z8,z5,z6]),(0,[z785,z2,z3,z8,z5,z6]),(0,[z1,z2,z532,z4,z5,z6]),(0,[z1,z2,z334,z4,z5,z6])],[(0,[z1,z2,z15,z3,z299,z6])],[(0,[z1,z2,z3,z8,z5,z786]),(0,[z1,z787,z3,z8,z5,z6]),(0,[z1,z2,z788,z8,z5,z6]),(0,[z1,z2,z358,z3,z5,z264]),(0,[z1,z2,z3,z789,z5,z6])],[(0,[z1,z2,z3,z790,z5,z6]),(0,[z1,z2,z3,z791,z5,z6])],[(0,[z1,z347,z3,z206,z5,z6]),(0,[z1,z792,z3,z8,z5,z6]),(0,[z7,z2,z3,z8,z736,z6]),(0,[z1,z2,z793,z3,z5,z6])],[(0,[z1,z2,z3,z8,z794,z6])]],
   [[(0,[z2,z3,z723,z8,z5,z6]),(0,[z1,z2,z795,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z266]),(0,[z175,z2,z3,z8,z736,z6]),(1,[z1,z3,z8,z769,z6]),(1,[z1,z3,z8,z5,z770])],[(0,[z1,z2,z3,z62,z5,z71]),(0,[z1,z2,z3,z4,z81,z6]),(0,[z26,z2,z3,z47,z5,z6])],[(0,[z1,z2,z796,z8,z5,z6]),(0,[z1,z2,z3,z8,z797,z6]),(0,[z1,z2,z3,z798,z5,z6]),(0,[z1,z2,z15,z3,z284,z6]),(0,[z1,z2,z3,z799,z5,z6]),(0,[z1,z2,z398,z4,z5,z6])],[],[(0,[z1,z347,z3,z383,z5,z6])],[(0,[z1,z2,z3,z62,z299,z6]),(0,[z1,z2,z3,z800,z5,z6]),(0,[z1,z801,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z802,z6]),(1,[z2,z3,z8,z5,z727])],[(0,[z1,z2,z3,z8,z803,z6]),(0,[z175,z2,z15,z3,z106,z6]),(0,[z1,z2,z3,z804,z5,z6]),(0,[z1,z2,z805,z3,z8,z6])]],
   [[(0,[z1,z2,z3,z8,z806,z6])],[(0,[z282,z2,z3,z8,z9,z6]),(0,[z1,z2,z807,z8,z5,z6]),(0,[z1,z2,z289,z3,z5,z6]),(0,[z1,z2,z808,z3,z4,z5]),(0,[z1,z2,z15,z320,z5,z6])],[(0,[z1,z2,z809,z8,z5,z6]),(0,[z1,z2,z3,z8,z299,z71]),(0,[z14,z225,z3,z8,z5,z266]),(0,[z1,z2,z810,z3,z5,z6]),(0,[z1,z2,z3,z8,z811,z6]),(0,[z110,z2,z115,z4,z5,z6]),(0,[z1,z2,z812,z8,z5,z6])],[(1,[z813,z3,z8,z5,z6]),(0,[z1,z2,z814,z8,z5,z6]),(0,[z503,z2,z3,z8,z9,z6]),(0,[z1,z2,z815,z8,z5,z6]),(0,[z1,z2,z85,z3,z5,z86])],[(0,[z1,z3,z8,z5,z770,z39])],[(0,[z1,z2,z152,z8,z81,z6]),(0,[z1,z2,z816,z3,z5,z6]),(0,[z1,z2,z4,z5,z589,z6])],[(0,[z1,z2,z817,z3,z5,z6]),(0,[z92,z1,z2,z3,z5,z6]),(0,[z31,z2,z3,z4,z5,z34]),(0,[z1,z2,z3,z5,z778,z86])],[(0,[z1,z2,z3,z5,z6,z818]),(0,[z2,z3,z8,z5,z736,z6]),(0,[z1,z2,z3,z96,z5,z6])]],
   [[(0,[z1,z2,z3,z819,z5,z6]),(0,[z1,z140,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z820]),(0,[z1,z2,z821,z3,z5,z6]),(0,[z1,z2,z15,z3,z5,z822])],[(0,[z1,z2,z723,z8,z5,z6]),(0,[z1,z2,z3,z823,z5,z6])],[(0,[z1,z2,z3,z824,z5,z6]),(0,[z1,z2,z825,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z826])],[(0,[z1,z2,z3,z827,z5,z6]),(0,[z1,z2,z3,z8,z5,z828]),(0,[z110,z2,z115,z8,z5,z6]),(0,[z1,z89,z114,z8,z5,z6])],[],[(0,[z1,z2,z152,z4,z5,z6]),(0,[z1,z2,z817,z367,z5,z6]),(0,[z1,z2,z15,z592,z5,z6])],[(0,[z1,z2,z829,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z830]),(0,[z1,z140,z3,z8,z493,z6]),(0,[z699,z2,z3,z8,z106,z6]),(0,[z1,z2,z3,z8,z831,z6]),(0,[z1,z2,z3,z5,z142,z778])]],
   [[(0,[z14,z225,z3,z8,z299,z6]),(0,[z1,z2,z3,z832,z5,z6])],[(0,[z27,z1,z3,z8,z37,z6]),(0,[z1,z2,z15,z3,z407,z6])],[(0,[z16,z813,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z326]),(0,[z1,z2,z833,z8,z5,z6]),(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z2,z835,z3,z5,z6]),(1,[z1,z2,z3,z5,z778]),(0,[z1,z2,z836,z3,z5,z6])],[(0,[z319,z1,z297,z193,z5,z6])],[(0,[z1,z2,z3,z8,z837,z6]),(0,[z1,z2,z838,z3,z5,z6]),(0,[z2,z3,z747,z4,z5,z6]),(0,[z839,z2,z3,z8,z5,z6])],[(0,[z1,z2,z367,z8,z5,z266]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z1,z2,z841,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z842])],[(0,[z1,z2,z152,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z174])],[(0,[z1,z2,z843,z8,z5,z6]),(0,[z1,z2,z3,z129,z844,z6])]],
   [[(0,[z1,z2,z3,z845,z5,z6]),(0,[z1,z2,z3,z8,z5,z846]),(0,[z1,z184,z3,z4,z5,z45]),(0,[z1,z2,z435,z4,z5,z6])],[(0,[z17,z813,z3,z8,z5,z6]),(0,[z1,z2,z3,z847,z5,z6]),(0,[z1,z2,z3,z8,z848,z6]),(0,[z1,z2,z3,z8,z5,z849]),(0,[z1,z2,z3,z8,z844,z6])],[(0,[z1,z259,z114,z8,z5,z6]),(0,[z1,z2,z850,z3,z4,z6]),(0,[z1,z2,z3,z53,z5,z6])],[(0,[z851,z2,z3,z8,z5,z6]),(0,[z1,z2,z852,z8,z5,z6]),(0,[z1,z2,z667,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z853])],[(0,[z1,z2,z3,z4,z5,z192]),(0,[z319,z1,z15,z193,z5,z6]),(0,[z1,z2,z364,z432,z5,z6]),(0,[z1,z2,z3,z5,z6,z854])],[(0,[z1,z2,z3,z8,z855,z6]),(0,[z1,z2,z3,z856,z5,z6])],[(0,[z1,z2,z3,z857,z5,z6])],[(0,[z26,z2,z3,z721,z5,z6]),(0,[z1,z2,z3,z858,z5,z6]),(0,[z1,z21,z3,z177,z5,z6])]],
   [[(0,[z14,z225,z3,z335,z5,z6]),(0,[z1,z2,z3,z859,z5,z6]),(0,[z1,z2,z3,z8,z213,z404]),(0,[z1,z2,z3,z8,z860,z6]),(0,[z151,z2,z3,z8,z5,z33])],[(0,[z14,z813,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z861,z6]),(0,[z1,z184,z3,z8,z5,z45]),(0,[z1,z2,z862,z3,z5,z6])],[(0,[z1,z2,z863,z8,z5,z6]),(0,[z1,z2,z703,z4,z5,z6]),(0,[z1,z2,z15,z42,z5,z58])],[(0,[z1,z2,z367,z8,z299,z6]),(0,[z1,z2,z3,z8,z493,z192]),(0,[z82,z2,z3,z70,z5,z6]),(0,[z1,z2,z3,z4,z213,z6]),(0,[z1,z2,z3,z80,z5,z6])],[(0,[z1,z2,z3,z5,z864,z6]),(0,[z1,z2,z3,z4,z5,z865])],[(0,[z866,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z192]),(0,[z1,z3,z8,z5,z6,z770])],[(0,[z1,z2,z867,z3,z5,z6])],[(0,[z868,z1,z2,z3,z5,z6]),(0,[z1,z140,z3,z206,z5,z6]),(0,[z1,z869,z3,z8,z5,z6]),(0,[z20,z2,z3,z70,z5,z6]),(0,[z870,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z206,z493,z6]),(0,[z1,z2,z749,z3,z8,z5]),(0,[z1,z21,z546,z177,z5,z6]),(0,[z1,z2,z3,z8,z5,z871]),(0,[z1,z2,z872,z3,z4,z6])],[(0,[z2,z115,z723,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z234]),(0,[z201,z1,z2,z3,z5,z286])],[(0,[z1,z2,z15,z3,z5,z873])],[(0,[z1,z2,z3,z8,z81,z266]),(0,[z1,z2,z15,z3,z5,z404]),(0,[z319,z1,z193,z222,z5,z6]),(0,[z1,z2,z4,z5,z6,z675]),(0,[z1,z2,z85,z3,z5,z491])],[(0,[z16,z17,z3,z4,z5,z6]),(0,[z46,z2,z723,z8,z5,z6]),(0,[z1,z2,z3,z8,z213,z6]),(0,[z1,z2,z874,z3,z5,z6]),(0,[z1,z2,z4,z190,z5,z6])],[(0,[z1,z2,z3,z8,z5,z865]),(0,[z38,z1,z3,z8,z5,z770])],[(0,[z1,z2,z3,z8,z5,z875]),(0,[z1,z2,z876,z3,z5,z6]),(0,[z1,z2,z297,z3,z5,z6])],[(0,[z1,z2,z877,z3,z5,z6]),(0,[z1,z2,z8,z878,z5,z6]),(0,[z1,z2,z3,z383,z5,z326])]],
   [[(0,[z351,z1,z193,z8,z5,z6]),(0,[z1,z2,z3,z879,z5,z6])],[(0,[z1,z2,z127,z8,z880,z6]),(0,[z1,z2,z294,z42,z5,z58])],[(0,[z1,z2,z3,z8,z5,z234])],[(0,[z1,z2,z367,z335,z5,z6]),(0,[z1,z2,z3,z8,z881,z6]),(0,[z1,z2,z3,z4,z5,z266]),(0,[z1,z2,z3,z8,z5,z882]),(0,[z1,z2,z3,z8,z5,z727]),(0,[z76,z1,z2,z15,z5,z6]),(0,[z1,z2,z3,z144,z5,z6]),(0,[z1,z2,z83,z144,z134,z6]),(0,[z1,z2,z3,z5,z6,z883])],[(0,[z1,z17,z114,z4,z5,z6]),(0,[z1,z347,z3,z8,z5,z192]),(0,[z1,z2,z15,z432,z5,z6]),(0,[z1,z2,z577,z3,z622,z6])],[(0,[z1,z884,z3,z8,z5,z6]),(0,[z7,z2,z3,z8,z9,z234]),(0,[z1,z2,z3,z8,z5,z885]),(0,[z1,z193,z728,z8,z5,z6]),(0,[z1,z3,z8,z5,z45,z770]),(0,[z1,z2,z3,z147,z5,z6]),(0,[z1,z2,z674,z3,z8,z79])],[(0,[z1,z225,z152,z8,z5,z6]),(0,[z1,z2,z3,z886,z5,z6]),(0,[z1,z2,z3,z887,z5,z6])],[(0,[z1,z2,z15,z3,z5,z6]),(0,[z888,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z213,z174]),(0,[z1,z2,z3,z8,z406,z33]),(0,[z1,z2,z432,z28,z5,z6]),(0,[z1,z21,z432,z177,z5,z6])]],
   [[],[(0,[z1,z2,z728,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z889]),(0,[z1,z2,z890,z3,z5,z6]),(0,[z1,z2,z3,z891,z5,z6])],[(0,[z1,z2,z3,z8,z5,z892]),(0,[z1,z2,z3,z8,z5,z893]),(0,[z7,z2,z15,z3,z9,z6]),(0,[z169,z2,z3,z8,z5,z33])],[(0,[z1,z347,z197,z8,z5,z6]),(0,[z1,z2,z3,z206,z5,z192]),(0,[z1,z2,z3,z4,z287,z6])],[(0,[z1,z2,z3,z164,z5,z6]),(0,[z1,z2,z127,z8,z128,z6])],[(0,[z1,z2,z3,z894,z5,z6]),(0,[z1,z2,z3,z895,z5,z6]),(0,[z1,z2,z548,z4,z5,z6]),(0,[z1,z2,z896,z3,z5,z6]),(0,[z1,z2,z301,z4,z5,z6])],[(0,[z1,z2,z15,z367,z5,z6]),(0,[z24,z2,z3,z47,z5,z6]),(0,[z1,z2,z897,z3,z5,z6]),(0,[z1,z2,z3,z4,z898,z6])],[(0,[z2,z813,z3,z8,z5,z6])]],
   [[(0,[z14,z225,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z899,z6]),(0,[z1,z2,z3,z4,z900,z5])],[(0,[z1,z2,z3,z4,z299,z6]),(0,[z1,z140,z3,z8,z287,z6])],[(0,[z1,z2,z3,z62,z5,z6]),(0,[z1,z2,z3,z8,z901,z6]),(0,[z1,z2,z3,z383,z5,z192]),(0,[z1,z2,z902,z8,z5,z6]),(0,[z1,z2,z3,z903,z5,z6]),(0,[z1,z2,z904,z3,z5,z6])],[(0,[z1,z2,z316,z4,z5,z6]),(0,[z1,z2,z734,z3,z4,z5]),(0,[z1,z2,z3,z844,z61,z6]),(0,[z1,z2,z3,z8,z905,z6])],[(0,[z1,z2,z3,z8,z287,z6]),(0,[z20,z2,z3,z721,z5,z6]),(0,[z2,z3,z8,z736,z9,z6]),(0,[z561,z2,z3,z8,z5,z34]),(0,[z1,z2,z3,z8,z906,z6]),(0,[z1,z2,z708,z3,z5,z6]),(0,[z1,z2,z4,z5,z51,z6])],[(0,[z1,z2,z3,z907,z5,z6]),(0,[z1,z2,z3,z908,z5,z6]),(0,[z1,z2,z3,z909,z5,z6]),(0,[z1,z89,z114,z4,z5,z6]),(0,[z1,z2,z3,z910,z5,z6]),(0,[z1,z2,z3,z8,z776,z6])],[(0,[z1,z2,z3,z8,z5,z71]),(0,[z1,z347,z15,z3,z5,z6]),(0,[z46,z2,z197,z4,z5,z6]),(0,[z1,z2,z3,z8,z284,z404]),(0,[z357,z2,z3,z8,z5,z33]),(0,[z1,z2,z3,z911,z5,z6]),(0,[z1,z2,z294,z3,z5,z6]),(0,[z1,z2,z415,z3,z5,z519]),(0,[z1,z2,z85,z3,z5,z519])],[(0,[z1,z2,z3,z5,z912,z6]),(0,[z1,z2,z3,z8,z898,z6]),(0,[z1,z556,z3,z8,z5,z45]),(0,[z1,z2,z105,z3,z844,z6]),(0,[z1,z2,z3,z913,z5,z6])]],
   [[(0,[z1,z2,z914,z3,z5,z6]),(0,[z26,z2,z3,z47,z5,z174]),(0,[z91,z2,z3,z8,z5,z33]),(0,[z1,z2,z915,z3,z5,z6])],[(0,[z1,z2,z3,z335,z81,z6]),(1,[z1,z728,z8,z5,z6]),(0,[z916,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z900,z5])],[(0,[z1,z2,z3,z8,z299,z6]),(0,[z1,z2,z114,z483,z5,z6]),(0,[z1,z2,z917,z3,z5,z6]),(0,[z918,z2,z3,z8,z5,z6])],[(0,[z14,z225,z3,z62,z5,z6]),(0,[z1,z508,z114,z8,z5,z6]),(0,[z1,z2,z3,z8,z919,z6])],[(0,[z1,z2,z3,z4,z5,z326]),(0,[z319,z1,z728,z8,z5,z6]),(0,[z1,z3,z775,z8,z5,z6])],[(0,[z46,z2,z197,z8,z493,z6]),(0,[z333,z2,z3,z8,z106,z6]),(0,[z1,z2,z708,z543,z5,z6]),(0,[z1,z2,z3,z8,z5,z920])],[(0,[z1,z2,z3,z147,z5,z34]),(0,[z1,z2,z808,z3,z8,z5]),(0,[z1,z2,z15,z101,z5,z6]),(0,[z1,z2,z42,z164,z5,z58])],[(0,[z14,z225,z3,z8,z5,z71]),(0,[z46,z2,z197,z8,z5,z6]),(0,[z1,z2,z3,z222,z5,z6]),(0,[z1,z2,z159,z4,z5,z6]),(0,[z1,z2,z346,z4,z5,z6])]],
   [[(0,[z1,z2,z921,z3,z5,z6]),(0,[z1,z2,z317,z3,z8,z79])],[(0,[z1,z2,z386,z3,z5,z6]),(0,[z1,z2,z85,z3,z5,z575])],[(0,[z1,z140,z3,z8,z5,z326]),(0,[z1,z2,z3,z8,z284,z6]),(0,[z1,z2,z620,z4,z5,z6]),(0,[z1,z2,z3,z922,z5,z6]),(0,[z1,z2,z289,z127,z128,z6]),(0,[z1,z2,z3,z8,z731,z79])],[(0,[z1,z2,z3,z8,z5,z923]),(0,[z1,z2,z382,z3,z5,z6]),(0,[z1,z347,z3,z8,z287,z6]),(0,[z1,z2,z3,z8,z493,z326]),(0,[z1,z2,z924,z3,z5,z6]),(0,[z1,z3,z8,z5,z769,z6])],[(0,[z1,z2,z3,z925,z5,z6]),(0,[z1,z2,z3,z8,z926,z5]),(0,[z1,z2,z15,z3,z406,z6]),(0,[z1,z2,z3,z927,z5,z6]),(0,[z1,z2,z3,z928,z5,z6])],[(0,[z26,z2,z3,z47,z213,z6]),(0,[z1,z2,z100,z3,z61,z6])],[(0,[z175,z2,z3,z8,z106,z6]),(0,[z1,z89,z114,z167,z5,z6]),(0,[z1,z2,z929,z8,z5,z6]),(0,[z1,z2,z8,z128,z880,z6])],[(0,[z1,z2,z3,z8,z930,z6]),(0,[z1,z2,z3,z931,z5,z6]),(0,[z1,z2,z3,z8,z6,z932]),(0,[z1,z2,z933,z3,z5,z6]),(0,[z1,z2,z934,z3,z5,z6])]],
   [[(0,[z1,z2,z15,z628,z5,z6]),(0,[z31,z2,z3,z8,z5,z727]),(0,[z1,z2,z15,z353,z5,z6]),(0,[z1,z2,z3,z8,z880,z6]),(0,[z1,z2,z317,z3,z8,z731])],[(0,[z1,z2,z672,z4,z5,z6])],[(0,[z1,z2,z3,z335,z5,z6]),(0,[z1,z2,z3,z206,z287,z6]),(0,[z38,z1,z15,z3,z5,z39])],[(0,[z1,z2,z3,z935,z5,z6])],[(0,[z1,z2,z3,z936,z5,z6]),(0,[z1,z2,z3,z8,z5,z937]),(0,[z1,z2,z938,z8,z5,z6])],[(0,[z14,z92,z225,z3,z5,z6]),(0,[z1,z3,z775,z177,z5,z6])],[(0,[z1,z2,z367,z62,z5,z6]),(0,[z46,z347,z197,z8,z5,z6]),(0,[z1,z2,z939,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z940]),(0,[z1,z2,z3,z8,z5,z941]),(0,[z1,z2,z4,z5,z148,z6]),(0,[z1,z2,z3,z8,z5,z822])]],
   [[(0,[z1,z2,z3,z8,z5,z942]),(0,[z262,z2,z3,z567,z5,z6])],[(0,[z1,z2,z877,z152,z5,z6]),(0,[z1,z2,z3,z8,z943,z6]),(0,[z1,z2,z3,z383,z287,z6]),(1,[z2,z3,z8,z736,z6]),(0,[z32,z2,z15,z3,z5,z33]),(0,[z1,z2,z3,z944,z5,z6]),(0,[z1,z2,z85,z3,z5,z778])],[(0,[z1,z2,z367,z8,z5,z71]),(0,[z1,z2,z15,z3,z5,z63])],[(0,[z1,z2,z3,z945,z5,z6]),(0,[z1,z2,z3,z5,z6,z946]),(0,[z1,z2,z154,z3,z5,z522]),(0,[z1,z2,z947,z3,z8,z6]),(0,[z1,z2,z83,z8,z880,z6])],[(0,[z1,z2,z3,z8,z5,z948]),(0,[z1,z347,z3,z8,z5,z326]),(0,[z1,z2,z100,z3,z844,z6])],[(0,[z1,z2,z3,z949,z5,z6]),(0,[z1,z140,z3,z8,z5,z192]),(0,[z1,z2,z3,z8,z950,z6]),(1,[z1,z2,z8,z880,z6])],[(0,[z1,z2,z3,z8,z5,z951]),(0,[z1,z2,z952,z8,z5,z6]),(0,[z110,z2,z723,z8,z5,z6])],[(0,[z211,z2,z3,z47,z5,z6]),(0,[z1,z89,z15,z114,z5,z6]),(0,[z1,z2,z114,z4,z5,z6]),(0,[z1,z36,z15,z3,z133,z6])]],
   [[(0,[z1,z2,z3,z8,z407,z6])],[(0,[z1,z2,z15,z152,z5,z6]),(0,[z1,z2,z15,z3,z81,z6]),(0,[z1,z2,z3,z8,z5,z953]),(0,[z1,z2,z954,z8,z5,z6]),(0,[z1,z2,z3,z8,z955,z6]),(0,[z1,z2,z956,z3,z5,z6]),(0,[z1,z2,z957,z8,z5,z6])],[(0,[z1,z2,z958,z8,z5,z6]),(0,[z1,z2,z3,z959,z5,z6]),(0,[z319,z1,z193,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z960]),(0,[z1,z2,z3,z206,z5,z326]),(0,[z1,z961,z3,z8,z5,z6]),(0,[z962,z1,z2,z3,z5,z6]),(0,[z1,z2,z471,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z778])],[(0,[z1,z2,z963,z3,z8,z5]),(0,[z46,z2,z197,z383,z5,z6]),(0,[z1,z2,z3,z964,z5,z6])],[(0,[z1,z2,z3,z965,z5,z6]),(0,[z1,z21,z3,z775,z5,z6]),(0,[z76,z1,z2,z708,z5,z6])],[(0,[z1,z2,z3,z8,z966,z6]),(0,[z1,z2,z714,z3,z5,z6]),(0,[z1,z2,z3,z129,z6,z576])],[(0,[z1,z2,z103,z4,z5,z119]),(0,[z1,z2,z805,z3,z4,z6]),(0,[z1,z2,z15,z3,z5,z967]),(0,[z1,z2,z154,z3,z5,z142])]],
   [[(0,[z1,z968,z3,z8,z5,z6])],[(0,[z1,z2,z263,z4,z5,z6]),(0,[z1,z2,z8,z5,z6,z969]),(0,[z1,z2,z3,z8,z5,z970]),(0,[z971,z2,z3,z8,z5,z6])],[(0,[z679,z2,z3,z8,z106,z6]),(0,[z132,z1,z3,z8,z769,z6])],[(0,[z1,z2,z3,z8,z972,z6]),(0,[z1,z2,z15,z288,z5,z6]),(0,[z26,z1,z2,z432,z5,z6]),(0,[z1,z2,z457,z4,z5,z6]),(0,[z973,z2,z3,z8,z5,z6])],[(0,[z1,z2,z974,z3,z5,z6]),(0,[z1,z2,z3,z62,z81,z6]),(0,[z207,z225,z3,z8,z5,z6]),(0,[z1,z2,z193,z483,z5,z6]),(0,[z1,z2,z3,z975,z5,z6]),(0,[z1,z2,z298,z3,z8,z79]),(0,[z1,z2,z976,z8,z5,z6]),(0,[z1,z2,z336,z4,z5,z6]),(0,[z1,z2,z3,z8,z977,z6]),(0,[z1,z2,z306,z3,z5,z73]),(0,[z1,z2,z15,z3,z715,z6]),(0,[z1,z2,z3,z8,z978,z6])],[(0,[z1,z2,z3,z8,z5,z979]),(0,[z1,z2,z372,z4,z5,z6]),(0,[z1,z2,z4,z387,z5,z6]),(0,[z1,z2,z629,z4,z5,z6]),(0,[z31,z2,z15,z3,z5,z34]),(0,[z312,z2,z3,z521,z5,z6])],[(0,[z2,z3,z8,z5,z6,z727]),(0,[z2,z3,z8,z5,z33,z727]),(0,[z1,z2,z127,z4,z128,z6]),(0,[z138,z2,z601,z3,z5,z6])],[(0,[z1,z140,z15,z3,z5,z6]),(0,[z261,z1,z2,z15,z5,z6]),(0,[z1,z2,z3,z980,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z81,z71]),(0,[z1,z2,z981,z8,z5,z6]),(0,[z1,z982,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z983]),(0,[z1,z2,z15,z3,z493,z6]),(0,[z1,z2,z984,z3,z5,z6]),(0,[z1,z2,z3,z985,z5,z6]),(0,[z1,z2,z3,z8,z986,z6]),(0,[z1,z2,z3,z8,z987,z6])],[(0,[z1,z2,z988,z8,z5,z6]),(0,[z1,z2,z297,z546,z5,z6])],[(0,[z1,z2,z3,z8,z989,z6]),(0,[z1,z347,z115,z8,z5,z6]),(0,[z1,z990,z3,z8,z5,z6]),(0,[z1,z2,z3,z991,z5,z6]),(0,[z1,z2,z3,z8,z992,z5]),(0,[z1,z2,z591,z3,z5,z6])],[(0,[z14,z382,z225,z3,z5,z6]),(0,[z1,z813,z3,z8,z5,z6]),(0,[z99,z2,z3,z8,z9,z6]),(0,[z1,z2,z3,z993,z5,z6]),(0,[z1,z2,z3,z8,z5,z994]),(0,[z1,z2,z3,z995,z5,z6]),(0,[z1,z2,z577,z3,z129,z6])],[(0,[z1,z2,z3,z996,z5,z6]),(0,[z1,z2,z997,z3,z8,z6]),(0,[z1,z2,z652,z4,z5,z6]),(0,[z1,z2,z364,z4,z5,z6]),(0,[z1,z2,z275,z3,z5,z6])],[(0,[z1,z2,z3,z8,z998,z6]),(0,[z1,z2,z3,z8,z5,z999]),(0,[z1,z2,z1000,z3,z5,z6]),(0,[z1,z2,z3,z5,z844,z6])],[(0,[z1,z2,z1001,z3,z5,z6]),(0,[z1,z490,z2,z15,z5,z6]),(0,[z495,z1,z620,z3,z5,z6])],[(0,[z1,z2,z3,z8,z1002,z6]),(0,[z1,z2,z3,z8,z5,z1003]),(0,[z1,z2,z599,z3,z8,z79]),(0,[z1,z2,z3,z8,z1004,z6])]],
   [[(0,[z1,z2,z1005,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z8,z5,z1006]),(0,[z1,z1007,z3,z8,z5,z6])],[(0,[z1,z2,z152,z8,z5,z266]),(0,[z1,z2,z3,z8,z5,z1008]),(0,[z2,z3,z721,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z1009]),(0,[z1,z2,z3,z8,z5,z873])],[(0,[z1,z2,z3,z8,z5,z1010]),(0,[z1,z2,z3,z8,z5,z404]),(0,[z1,z2,z1011,z8,z5,z6]),(0,[z1,z2,z15,z546,z5,z6])],[(0,[z1,z2,z3,z1012,z5,z6]),(0,[z1,z2,z1013,z3,z5,z6]),(0,[z1,z2,z1014,z3,z5,z6]),(0,[z1,z2,z714,z193,z5,z6]),(0,[z1,z2,z317,z3,z147,z79])],[(0,[z1,z89,z114,z96,z5,z6]),(0,[z1,z2,z3,z5,z142,z258])],[(0,[z1,z2,z15,z3,z5,z174]),(0,[z1,z2,z574,z8,z134,z6]),(0,[z1,z2,z1015,z3,z5,z6])],[(0,[z262,z2,z3,z70,z5,z6])],[(0,[z1,z225,z114,z4,z5,z6]),(0,[z1,z2,z1016,z3,z5,z6]),(0,[z1,z2,z3,z8,z1017,z6]),(0,[z1,z2,z574,z4,z5,z6]),(0,[z1,z2,z1018,z3,z5,z6]),(0,[z1,z2,z607,z4,z5,z6]),(0,[z1,z2,z3,z5,z778,z6])]],
   [[(0,[z1,z2,z494,z4,z5,z6]),(0,[z1,z2,z15,z127,z128,z6]),(0,[z1,z2,z100,z3,z458,z6])],[(0,[z1,z2,z3,z8,z5,z1019]),(0,[z1,z36,z3,z8,z769,z6]),(0,[z1,z2,z100,z3,z409,z6]),(0,[z1,z1020,z3,z8,z5,z6])],[],[(0,[z1,z2,z297,z4,z5,z6]),(0,[z132,z1,z15,z3,z37,z6]),(0,[z1,z2,z1021,z3,z5,z6])],[(0,[z1,z2,z3,z4,z284,z6])],[(0,[z1,z2,z1022,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z732,z5,z6]),(0,[z1,z2,z3,z8,z5,z1023]),(0,[z1,z2,z1024,z3,z5,z6]),(0,[z1,z2,z83,z8,z134,z6])],[(0,[z1,z2,z152,z8,z299,z6]),(0,[z46,z140,z197,z8,z5,z6]),(0,[z1,z2,z105,z3,z381,z6]),(0,[z1,z2,z3,z1025,z5,z6]),(0,[z1,z2,z15,z571,z5,z6])]],
   [[(0,[z1,z2,z3,z1026,z5,z6]),(0,[z1,z2,z15,z466,z5,z6]),(0,[z1,z2,z1027,z8,z5,z6]),(0,[z175,z2,z3,z4,z106,z6]),(0,[z1,z2,z3,z8,z1028,z6])],[(0,[z319,z1,z372,z8,z5,z6]),(1,[z2,z723,z8,z5,z6]),(0,[z7,z2,z3,z8,z9,z6]),(0,[z1,z2,z193,z4,z5,z6]),(0,[z1,z2,z696,z4,z5,z6])],[(0,[z1,z2,z1029,z3,z5,z6])],[(0,[z97,z1,z233,z3,z5,z6]),(0,[z1,z2,z3,z1030,z5,z6]),(0,[z1,z2,z3,z4,z1031,z6])],[(0,[z1,z2,z15,z4,z5,z6])],[(0,[z1,z2,z185,z4,z5,z6]),(0,[z1,z2,z1032,z8,z5,z6])],[(0,[z1,z2,z1033,z8,z5,z6])],[(0,[z14,z225,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z106,z234]),(0,[z1,z2,z546,z8,z5,z6]),(0,[z1,z223,z193,z8,z5,z6]),(0,[z1,z2,z3,z1034,z5,z6]),(0,[z1,z2,z8,z5,z880,z6])]],
   [[(0,[z1,z2,z3,z8,z287,z192]),(0,[z280,z1,z3,z8,z5,z39])],[(0,[z1,z2,z3,z1035,z5,z6]),(0,[z1,z2,z15,z108,z5,z6])],[(0,[z1,z2,z3,z8,z1036,z6]),(0,[z1,z2,z3,z147,z106,z6]),(0,[z1,z2,z3,z1037,z5,z6]),(0,[z1,z2,z370,z4,z5,z6])],[(0,[z1,z2,z1038,z3,z5,z6]),(0,[z16,z17,z15,z3,z5,z6]),(0,[z1,z2,z3,z8,z1039,z6]),(1,[z2,z3,z721,z5,z6]),(0,[z1,z2,z3,z8,z5,z1040]),(0,[z1,z2,z317,z3,z57,z79])],[(0,[z1,z2,z3,z8,z1031,z6])],[(0,[z1,z2,z3,z1041,z5,z6]),(0,[z1,z2,z1042,z3,z5,z6])],[(0,[z1,z2,z1043,z8,z5,z6]),(0,[z1,z2,z3,z8,z1044,z6]),(0,[z46,z2,z15,z197,z5,z6])],[(0,[z1,z2,z152,z335,z5,z6]),(0,[z1,z2,z317,z15,z3,z79]),(0,[z1,z2,z1045,z8,z5,z6]),(0,[z1,z2,z1046,z3,z5,z6])]],
   [[(0,[z1,z17,z152,z8,z5,z6]),(0,[z1,z2,z3,z8,z284,z174]),(0,[z1,z2,z3,z1047,z5,z6]),(0,[z1,z2,z3,z8,z1048,z6]),(0,[z1,z157,z3,z64,z5,z6])],[(0,[z1,z2,z3,z8,z1049,z6]),(0,[z1,z2,z367,z4,z5,z6]),(0,[z1,z2,z516,z3,z8,z79]),(0,[z1,z2,z708,z4,z5,z6])],[(0,[z1,z2,z15,z3,z5,z266]),(0,[z1,z2,z1050,z3,z5,z6]),(0,[z1,z2,z3,z4,z406,z6]),(0,[z1,z2,z3,z4,z407,z6])],[(0,[z46,z2,z197,z8,z5,z192]),(0,[z1,z181,z3,z8,z133,z6]),(0,[z1,z2,z42,z8,z5,z740])],[(0,[z1,z2,z3,z1051,z5,z6]),(0,[z1,z348,z3,z177,z5,z6]),(0,[z1,z2,z3,z1052,z5,z6]),(0,[z319,z1,z193,z4,z5,z6]),(0,[z1,z2,z3,z1053,z5,z6])],[(0,[z1,z2,z3,z8,z1054,z6]),(0,[z1,z2,z8,z5,z1055,z6]),(0,[z1,z2,z3,z1056,z5,z6]),(0,[z1,z2,z3,z5,z6,z1057])],[(0,[z813,z225,z3,z8,z5,z6]),(0,[z2,z3,z721,z70,z5,z6]),(0,[z31,z2,z3,z8,z406,z34]),(0,[z31,z2,z3,z8,z407,z34]),(0,[z1,z2,z114,z96,z5,z6]),(0,[z1,z193,z114,z4,z5,z6]),(0,[z1,z2,z432,z8,z5,z6]),(0,[z1,z2,z358,z3,z5,z142])],[(0,[z1,z2,z3,z8,z5,z1058]),(0,[z1,z2,z3,z8,z5,z1059])]],
   [[(0,[z46,z2,z197,z206,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1060])],[(0,[z1,z2,z367,z8,z5,z6]),(0,[z1,z2,z15,z3,z287,z6]),(0,[z1,z2,z850,z3,z8,z6]),(0,[z1,z2,z1061,z3,z5,z6]),(0,[z1,z2,z708,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1062])],[(0,[z1,z2,z3,z383,z5,z6]),(0,[z1,z2,z3,z483,z5,z6]),(0,[z1,z2,z3,z8,z5,z1063]),(0,[z1,z2,z3,z8,z406,z6]),(0,[z1,z2,z300,z8,z128,z6])],[(0,[z1,z2,z1064,z3,z8,z5])],[(0,[z1,z2,z3,z62,z5,z266]),(0,[z1,z1065,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1066]),(0,[z1,z2,z3,z5,z6,z1067])],[(0,[z1,z114,z212,z4,z5,z6])],[(0,[z32,z2,z3,z4,z5,z33]),(0,[z1,z2,z105,z3,z50,z6]),(0,[z1,z2,z83,z275,z134,z6])]],
   [[(0,[z1,z1068,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z63]),(0,[z1,z2,z100,z3,z545,z6]),(0,[z1,z157,z114,z8,z5,z6])],[(0,[z1,z2,z1069,z3,z5,z6]),(0,[z38,z1,z3,z8,z5,z39])],[(0,[z1,z2,z3,z1070,z5,z6]),(0,[z1,z2,z1071,z3,z5,z6]),(0,[z1,z2,z209,z3,z61,z6]),(0,[z1,z2,z3,z1072,z5,z6])],[(0,[z1,z2,z367,z745,z5,z6]),(0,[z14,z225,z367,z8,z5,z6]),(0,[z649,z2,z3,z8,z5,z34]),(0,[z1,z2,z185,z8,z5,z58])],[(0,[z26,z10,z2,z3,z5,z6]),(0,[z1,z2,z3,z1073,z5,z6])],[(0,[z1,z2,z3,z8,z1074,z6]),(0,[z1,z2,z3,z8,z299,z266]),(0,[z1,z2,z3,z8,z1075,z6]),(0,[z1,z36,z3,z4,z133,z6]),(0,[z1076,z1,z3,z8,z5,z6])],[],[(0,[z1,z2,z432,z177,z5,z6]),(0,[z1,z2,z3,z8,z1077,z6]),(0,[z1,z2,z3,z5,z6,z57])]],
   [[(0,[z1,z2,z1078,z8,z5,z6]),(0,[z1,z2,z1079,z3,z5,z6]),(0,[z112,z17,z3,z8,z5,z6]),(0,[z1,z2,z3,z1080,z5,z6]),(0,[z32,z2,z3,z8,z5,z33]),(0,[z1,z2,z872,z3,z8,z6]),(0,[z1,z2,z3,z8,z1081,z6]),(0,[z1,z21,z620,z3,z5,z6]),(0,[z1,z2,z15,z3,z831,z6])],[(0,[z1,z2,z3,z8,z5,z1082]),(0,[z1,z2,z3,z8,z5,z63]),(0,[z1,z2,z3,z1083,z5,z6])],[(0,[z1,z2,z3,z8,z1084,z6]),(0,[z20,z2,z601,z3,z5,z6]),(0,[z1,z2,z3,z8,z1085,z6]),(0,[z1086,z2,z3,z8,z5,z6]),(0,[z1,z2,z154,z3,z5,z286]),(0,[z1,z2,z3,z1087,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1088]),(0,[z1089,z1,z2,z3,z5,z6]),(0,[z1,z2,z15,z3,z5,z326]),(0,[z1,z2,z1090,z3,z5,z6]),(0,[z1,z2,z543,z4,z5,z6]),(0,[z1,z2,z3,z1091,z5,z6])],[(0,[z1,z2,z1092,z3,z5,z6]),(0,[z1,z1093,z3,z8,z5,z6]),(0,[z20,z2,z648,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z404]),(0,[z7,z2,z3,z8,z9,z63]),(0,[z1,z2,z3,z8,z1094,z6]),(0,[z1,z3,z8,z769,z37,z6]),(0,[z1,z2,z470,z4,z5,z6])],[(0,[z1,z2,z3,z1095,z5,z6]),(0,[z1,z2,z3,z1096,z5,z6]),(0,[z1097,z2,z3,z8,z5,z6]),(0,[z1098,z2,z3,z8,z5,z6]),(0,[z1,z184,z3,z8,z5,z770])],[(0,[z1,z2,z3,z8,z1099,z6]),(0,[z26,z2,z3,z47,z284,z6]),(0,[z492,z2,z3,z8,z106,z6]),(0,[z1,z36,z3,z8,z133,z6]),(0,[z1,z2,z8,z880,z134,z6])],[(0,[z1,z2,z1100,z8,z5,z6]),(0,[z1,z2,z3,z1101,z5,z6]),(0,[z1,z2,z40,z3,z409,z6])]],
   [[(0,[z1,z2,z3,z8,z81,z6]),(0,[z1102,z2,z3,z8,z5,z6]),(0,[z1,z2,z317,z3,z4,z79]),(1,[z1,z2,z3,z844,z6])],[(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z68,z114,z8,z5,z6]),(0,[z1,z2,z3,z147,z5,z33])],[(0,[z46,z2,z197,z8,z287,z6])],[(0,[z1,z2,z3,z8,z1104,z6]),(0,[z1,z2,z3,z8,z5,z1105]),(0,[z1,z2,z3,z1106,z5,z6])],[(0,[z1,z2,z402,z4,z5,z6]),(0,[z1,z2,z3,z8,z406,z34]),(0,[z1,z2,z626,z4,z5,z6]),(0,[z718,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1107,z5,z6]),(0,[z1,z2,z15,z3,z5,z853])],[(0,[z1,z2,z3,z335,z5,z266]),(0,[z1,z2,z1108,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z1109])],[(0,[z1,z2,z3,z4,z493,z6]),(0,[z1,z2,z3,z1110,z5,z6]),(0,[z186,z1,z2,z3,z50,z6]),(0,[z1,z2,z15,z3,z855,z6]),(0,[z1,z2,z3,z8,z5,z967])],[(0,[z1,z2,z1111,z8,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 542) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 542).take 540) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1082).take 73) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1155)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [542, 540, 73] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 148).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 148).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [148, 108] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_43818

theorem PEqualNP.Outside.L_meta_43818 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276799624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276799624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43818.solve