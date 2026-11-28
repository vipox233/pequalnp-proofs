import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43166

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
  Nat.testBit (4276808362 * 2 ^ 32 + 4007714816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00005055530f0f0e#64 ++ 0x0000141554c3c3c3#64 ++ 0xe011f1fff71f1f1d#64 ++ 0xf8047c7ffdc7c7c7#64 : BitVec 256),
   (0x2066c6ccc3636360#64 ++ 0x0819b1b330d8d8d8#64 ++ 0xe0eececccbe3e3e3#64 ++ 0x783bb3b332f8f8f8#64 : BitVec 256),
   (0x170b0b0f0c01b5b4#64 ++ 0x05c2c2c3c3006d6d#64 ++ 0xff0f0f0f0c03ffff#64 ++ 0xbfc3c3c3c300ffff#64 : BitVec 256),
   (0x4bb00df00db402d8#64 ++ 0x12ec037c036d00b6#64 ++ 0x7ff00ff00ffc03ff#64 ++ 0xdffc03fc03ff00ff#64 : BitVec 256),
   (0x8dddf0000edad800#64 ++ 0x23777c0003b6b600#64 ++ 0xbffff0000ffffc03#64 ++ 0xeffffc0003ffff00#64 : BitVec 256),
   (0x0effafaaa0000000#64 ++ 0x43bfebeaa8000000#64 ++ 0xdffffffff0000003#64 ++ 0xf7fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xe011f1fff71f1f1d 0xf8047c7ffdc7c7c7

def z1 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xdffffffff0000003 0xf7fffffffc000000

def z2 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff0f0f0f0c03ffff 0xbfc3c3c3c300ffff

def z3 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x20ee0e000be3e3e2 0x083b838002f8f8f8

def z4 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x7ff00ff00ffc03ff 0xdffc03fc03ff00ff

def z5 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xbffff0000ffffc03 0xeffffc0003ffff00

def z6 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0eececccbe3e3e3 0x783bb3b332f8f8f8

def z7 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0xfff1fffffffc03ff 0xfffc7fffffff00ff

def z8 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0ffffffffffffff 0xf83fffffffffffff

def z9 : W := mkw 0x4bb05df55fbf0fde 0x12ec177d57efc3f7 0xfff1ffffffff1fff 0xfffc7fffffffc7ff

def z10 : W := mkw 0x28f4e4e0e3624240 0x4a3d393838d89090 0x00f0f0f0f3e00000 0x403c3c3c3cf80000

def z11 : W := mkw 0x0af68fa880000000 0x02bda3ea20000000 0xdffecffcc0000003 0xf7ffb3ff30000000

def z12 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x1ffefef0f0000002 0x47ffbfbc3c000000

def z13 : W := mkw 0x0000000100000404 0x0000000040000101 0x0001010304001c1c 0x80004040c1000707

def z14 : W := mkw 0x2000404043624240 0x0800101010d89090 0x0000000003e00000 0x0000000000f80000

def z15 : W := mkw 0x002004c001200240 0x0008013000480090 0x60e00ec00be003e3 0x583803b002f800f8

def z16 : W := mkw 0x0044c00002424000 0x0011300000909000 0xa0eec0000be3e003 0x683bb00002f8f800

def z17 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x3f0e0e000c03fffe 0x0fc383800300ffff

def z18 : W := mkw 0x0066868880000000 0x0019a1a220000000 0x00ee0e0000000002 0x003b838000000000

def z19 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x00ee0e0008e0e0e2 0x003b838002383838

def z20 : W := mkw 0x0066868880000000 0x0019a1a220000000 0xc0eececcc0000003 0x703bb3b330000000

def z21 : W := mkw 0x1102020d0c01b5b4 0x0440808343006d6d 0xe00e0e0c0c03ffff 0x380383830300ffff

def z22 : W := mkw 0x8ddda0000cd0d000 0x2377680003343400 0x1fee000008e0e002 0x07fb800002383800

def z23 : W := mkw 0x140b020f0001b524 0x0502c083c0006d49 0x800f000f0003fc00 0x2003c003c000ff00

def z24 : W := mkw 0x20005055536f6f6e 0x0800141554dbdbdb 0x200000000ffffffc 0x0800000003ffffff

def z25 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x9ffffe0000000003 0xe7ffff8000000000

def z26 : W := mkw 0x0000405443070308 0x0000101510c1c0c2 0xe010c1fcc71f031d 0xf804307f31c7c0c7

def z27 : W := mkw 0x000000555105070e 0x00000015544141c3 0x400001fff000031c 0x1000007ffc0000c7

def z28 : W := mkw 0x8fffffaaaedad800 0x63ffffeaabb6b600 0xfffffffffffffc03 0xffffffffffffff00

def z29 : W := mkw 0x2066c6c8c3624240 0x0819b1b230d89090 0xc0eececcc3e00003 0x703bb3b330f80000

def z30 : W := mkw 0x2044c04443636360 0x0811301110d8d8d8 0xa0eec0000be3e3e3 0x683bb00002f8f8f8

def z31 : W := mkw 0x206686c881606260 0x0819a1b220581898 0x60ee0ec00be0e3e3 0x583b83b002f838f8

def z32 : W := mkw 0x000000555105070e 0x00000015544141c3 0xc011f1fff000031d 0xf0047c7ffc0000c7

def z33 : W := mkw 0x8044f000024a4800 0x20113c0000929200 0x0000f00000000000 0x00003c0000000000

def z34 : W := mkw 0x062b0faaa0000000 0x418ac3eaa8000000 0xdf0f0ffff0000003 0xb7c3c3fffc000000

def z35 : W := mkw 0x0edfab2aa0000000 0x43b7eacaa8000000 0x9f1ff13ff0000000 0xa7c7fc4ffc000000

def z36 : W := mkw 0x110000050c01b5b4 0x0440000143006d6d 0x200000000c03fffc 0x080000000300ffff

def z37 : W := mkw 0x170b5b0f0e0bbdb4 0x05c2d6c3c382ef6d 0xff1fff0f0f1fffff 0xffc7ffc3c3c7ffff

def z38 : W := mkw 0x2046c24cc3636360 0x0811b09330d8d8d8 0xa00ec00ccbe3e3e0 0x2803b00332f8f8f8

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x0011313330000000 0x80044c4ccc000000

def z40 : W := mkw 0x044fa20aa0000000 0x4113e882a8000000 0x800ff00ff0000000 0x2003fc03fc000000

def z41 : W := mkw 0x170b0b0a0c00b0b0 0x05c2c2c283002c2c 0xdf0f0f0f0800e0e3 0xb7c3c3c3c2003838

def z42 : W := mkw 0x8ddda0000cd0d000 0x2377680003343400 0xbfef00000ce3fc03 0xaffbc0000338ff00

def z43 : W := mkw 0x00005005520b0d06 0x000014015482c341 0x8001f00ff0031c00 0x20007c03fc00c700

def z44 : W := mkw 0x376f8f8f8c61f5f4 0x0ddbe3e3e3187d7d 0xffef0f0f0ce3ffff 0xbffbc3c3c338ffff

def z45 : W := mkw 0x060b0b0a00000000 0x0182c2c280000000 0xdf0f0f0f00000003 0xb7c3c3c3c0000000

def z46 : W := mkw 0x0fffafaaac000090 0x43ffebeaab000024 0xfffffffffc0003ff 0xffffffffff0000ff

def z47 : W := mkw 0x050900000c009000 0x0142400003002400 0xbf0f00000c03fc03 0xafc3c0000300ff00

def z48 : W := mkw 0x8d9930000c989800 0x23664c0003262600 0x1f113000041c1c00 0x87c44c0001070700

def z49 : W := mkw 0x0066868880000000 0x0019a1a220000000 0xc0fffffff0000003 0xf03ffffffc000000

def z50 : W := mkw 0x0000005001040208 0x0000001400410082 0x601001f0071c031d 0xd804007c01c700c7

def z51 : W := mkw 0x2000000000606060 0x0800000000181818 0x0000000008e0e0e0 0x0000000002383838

def z52 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x20000000071f1f1c 0x0800000001c7c7c7

def z53 : W := mkw 0x810050000edad800 0x2040140003b6b600 0x200000000ffffc00 0x0800000003ffff00

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0xa001000004031c01 0xa80040000100c700

def z55 : W := mkw 0x42200df5512507de 0x1088037d544941f7 0x40000ffff00003fc 0x100003fffc0000ff

def z56 : W := mkw 0x2000404443636360 0x0800101110d8d8d8 0x200000000be3e3e0 0x0800000002f8f8f8

def z57 : W := mkw 0x20005055536f6f6e 0x0800141554dbdbdb 0xe011f1fffffffffd 0xf8047c7fffffffff

def z58 : W := mkw 0x410000500db402d8 0x10400014036d00b6 0x200000000ffc03fc 0x0800000003ff00ff

def z59 : W := mkw 0x4fffaffaadb402d8 0x53ffebfeab6d00b6 0xfffffffffffc03ff 0xffffffffffff00ff

def z60 : W := mkw 0x0409000000009000 0x0102400000002400 0x800f00000003fc00 0x2003c0000000ff00

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0xc011f1fff0000001 0xf0047c7ffc000000

def z62 : W := mkw 0x00001011100c0c0e 0x0000040444030303 0x00113133341c1c1c 0x80044c4ccd070707

def z63 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x9feff00008e3fc02 0x27fbfc000238ff00

def z64 : W := mkw 0x170909030c009494 0x05c24240c3002525 0x1f01010304001c1c 0x87c04040c1000707

def z65 : W := mkw 0x2064c4c0c3624240 0x0819313030d89090 0x00e0c0c0c3e00000 0x4038303030f80000

def z66 : W := mkw 0x68f4c4f0c3f64248 0x1a3d313c30fd9092 0x00f0c0f0c3fc0000 0x403c303c30ff0000

def z67 : W := mkw 0x0e99292220000000 0x43a64a4888000000 0x1f00000000000000 0x07c0000000000000

def z68 : W := mkw 0x4bb00da00cb000d0 0x12ec0368032c0034 0x1fe00e0008e000e2 0x07f8038002380038

def z69 : W := mkw 0x5fffafffadb5b7fc 0x57ffebffeb6d6dff 0xffffffffffffffff 0xffffffffffffffff

def z70 : W := mkw 0x0d9900000c909000 0x0366400003242400 0xbfff00000ffffc03 0xefffc00003ffff00

def z71 : W := mkw 0x5fbb0fff0db5b7fc 0x17eec3ffc36d6dff 0xffff0fff0fffffff 0xffffc3ffc3ffffff

def z72 : W := mkw 0x170909030c009494 0x05c24240c3002525 0xbf0f01030c03fc1f 0xafc3c040c300ff07

def z73 : W := mkw 0x00005050530e0a0a 0x0000141414c38282 0x0010f0f0f31c0000 0x40043c3c3cc70000

def z74 : W := mkw 0xbfffffcfcffbfff4 0x2ffffff3f3fefffd 0xffffffcfcfffffff 0xfffffff3f3ffffff

def z75 : W := mkw 0x030009000c000090 0x00c0024003000024 0x7f000f000c0003ff 0x9fc003c0030000ff

def z76 : W := mkw 0x0fffafaaac900000 0x43ffebeaab240000 0xfffffffffffc0003 0xffffffffffff0000

def z77 : W := mkw 0x1f9b0b0f0c91b5b4 0x07e6c2c3c3246d6d 0xffff0f0f0fffffff 0xffffc3c3c3ffffff

def z78 : W := mkw 0x02220ffff105070e 0x408883fffc4141c3 0x40000ffff000031c 0x100003fffc0000c7

def z79 : W := mkw 0x9fdffb0f0edbfdb4 0x27f7fec3c3b6ff6d 0xffffff0f0fffffff 0xffffffc3c3ffffff

def z80 : W := mkw 0x4b9009700db402d8 0x12e4025c036d00b6 0x3f1001300ffc03fc 0x8fc4004c03ff00ff

def z81 : W := mkw 0x140b020f0001b524 0x0502c083c0006d49 0xe00f0e0f0803ffe3 0x3803c383c200fff8

def z82 : W := mkw 0x0cdda00000000000 0x0337680000000000 0x9ffff00000000003 0xe7fffc0000000000

def z83 : W := mkw 0x0000404443030300 0x0000101110c0c0c0 0x2000000003030300 0x0800000000c0c0c0

def z84 : W := mkw 0x0002020c00012120 0x0000808300004848 0xe00e0e0c0803e3e3 0x380383830200f8f8

def z85 : W := mkw 0x4fbb0ffa0db402d8 0x13eec3fe836d00b6 0xffff0fff0ffc03ff 0xffffc3ffc3ff00ff

def z86 : W := mkw 0x844df000024ad800 0x21137c000092b600 0x800ff0000003fc00 0x2003fc000000ff00

def z87 : W := mkw 0x0000000550010506 0x0000000154004141 0x0000000ff0000000 0x00000003fc000000

def z88 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x5fee0ffff0000002 0x17fb83fffc000000

def z89 : W := mkw 0x202246ccc3636360 0x080891b330d8d8d8 0x60000ecccbe3e3e0 0x180003b332f8f8f8

def z90 : W := mkw 0x202206ccc1212360 0x080881b3304848d8 0xe00e0eccc803e3e3 0x380383b33200f8f8

def z91 : W := mkw 0x202206ccc1212360 0x080881b3304848d8 0x40000eccc00003e0 0x100003b3300000f8

def z92 : W := mkw 0x0ab00da000000000 0x02ac036800000000 0x5ff00ff000000003 0xd7fc03fc00000000

def z93 : W := mkw 0x02220faaa0000000 0x408883eaa8000000 0x00000e0000000000 0x0000038000000000

def z94 : W := mkw 0x0064848080000000 0x0019212020000000 0x00e0c0c0c0000000 0x4038303030000000

def z95 : W := mkw 0x910050050edbfdb4 0x2440140143b6ff6d 0x200000000ffffffc 0x0800000003ffffff

def z96 : W := mkw 0x0edda92220000000 0x43b76a4888000000 0x9ffff13330000003 0xe7fffc4ccc000000

def z97 : W := mkw 0x0cdfa20aa0000000 0x4337e882a8000000 0x9ffff00ff0000003 0xe7fffc03fc000000

def z98 : W := mkw 0x170b1b1f1c0dbdbe 0x05c2c6c7c7036f6f 0xff1f3f3f3c1fffff 0xbfc7cfcfcf07ffff

def z99 : W := mkw 0x2effefeee3636360 0x4bbffbfbb8d8d8d8 0xfffffffffbe3e3e3 0xfffffffffef8f8f8

def z100 : W := mkw 0x374fcb0fce43f5b4 0x0dd3f2c3f390fd6d 0xff0fcf0fcc03ffff 0xbfc3f3c3f300ffff

def z101 : W := mkw 0x09b004c00db00240 0x026c0130036c0090 0x7ff00ec00ffc03e3 0xdffc03b003ff00f8

def z102 : W := mkw 0x4b9009300c940098 0x12e4024c03250026 0x3ff001300ffc001f 0xcffc004c03ff0007

def z103 : W := mkw 0x0064c4c003624240 0x0019313000d89090 0xe0eecec00be3e3e3 0x783bb3b002f8f8f8

def z104 : W := mkw 0xcffdfdf00ffedad8 0x33ff7f7c03ffb6b6 0xfffffff00fffffff 0xfffffffc03ffffff

def z105 : W := mkw 0x42200df0012402d8 0x1088037c004900b6 0x40000ff0000003fc 0x100003fc000000ff

def z106 : W := mkw 0x974ffb0f0e4bfdb4 0x25d3fec3c392ff6d 0xff0fff0f0c03ffff 0xbfc3ffc3c300ffff

def z107 : W := mkw 0x0efffffff30f0f0e 0x43bffffffcc3c3c3 0xfffffffff71f1f1f 0xfffffffffdc7c7c7

def z108 : W := mkw 0x410000000cb000d0 0x10400000032c0034 0x0000000008e000e0 0x0000000002380038

def z109 : W := mkw 0x5fbb0faa0cb0b0f0 0x17eec3ea832c2c3c 0x1fee0e0008e0e0e2 0x07fb838002383838

def z110 : W := mkw 0x000000555105070e 0x00000015544141c3 0xe00101fff4031f1d 0xb800407ffd00c7c7

def z111 : W := mkw 0x00005044430b0b00 0x0000141110c2c2c0 0xe011f0ccc71f1f01 0xf8047c3331c7c7c0

def z112 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff1ffffffc03ffff 0xffc7ffffff00ffff

def z113 : W := mkw 0x0002020c00012120 0x0000808300004848 0x40000e0c000003e0 0x10000383000000f8

def z114 : W := mkw 0x0cffa68880000000 0x033fe9a220000000 0xdffffeccc0000003 0xf7ffffb330000000

def z115 : W := mkw 0x0efdada000000000 0x03bf6b6800000000 0xdffffff000000003 0xf7fffffc00000000

def z116 : W := mkw 0x0002424c43032320 0x0000909310c0c8c8 0xe00ececccb03e3e3 0x7803b3b332c0f8f8

def z117 : W := mkw 0x0000005001040208 0x0000001400410082 0x001000f0031c0000 0x4004003c00c70000

def z118 : W := mkw 0x0cffa6aaa0000000 0x433fe9aaa8000000 0x80fff0fff0000000 0x603ffc3ffc000000

def z119 : W := mkw 0x002206cc01212360 0x000881b3004848d8 0xe0ee0ecc0be3e3e3 0x783b83b302f8f8f8

def z120 : W := mkw 0x410050555fbf0fde 0x1040141557efc3f7 0x200000000fff1ffc 0x0800000003ffc7ff

def z121 : W := mkw 0x52220fff012527fc 0x148883ffc04949ff 0x40000fff000003fc 0x100003ffc00000ff

def z122 : W := mkw 0x00001051110c0e0e 0x0000041444430383 0x601131f3371c1f1d 0xd8044c7ccdc707c7

def z123 : W := mkw 0x070909000c009090 0x01c2424003002424 0xff0f0f000c03ffff 0xbfc3c3c00300ffff

def z124 : W := mkw 0x0044d000024a4800 0x0011340000929200 0xa0fff0000ffffc03 0xe83ffc0003ffff00

def z125 : W := mkw 0xadfff6dddfffff6e 0x2b7ffdb777ffffdb 0xffffffffffffffff 0xffffffffffffffff

def z126 : W := mkw 0x8fffafaaacd0d000 0x63ffebeaab343400 0xdffffffff8e0e003 0xf7fffffffe383800

def z127 : W := mkw 0x160b0b0f0001b524 0x0582c2c3c0006d49 0xdf0f0f0f0003fc03 0xb7c3c3c3c000ff00

def z128 : W := mkw 0x0e99292220000000 0x43a64a4888000000 0xdf11f1fff0000001 0xf7c47c7ffc000000

def z129 : W := mkw 0x0044a000a0000000 0x4011280028000000 0x0000f000f0000000 0x00003c003c000000

def z130 : W := mkw 0x0e99292220000000 0x43a64a4888000000 0x1f11313330000000 0x87c44c4ccc000000

def z131 : W := mkw 0x08f6a6a8a0000000 0x423da9aa28000000 0xc0fefefcf0000003 0x703fbfbf3c000000

def z132 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x80eec0ccc3e3e000 0x603bb03330f8f800

def z133 : W := mkw 0x89d4f0000eda4800 0x22753c0003b69200 0x3ff0f0000ffc0003 0xcffc3c0003ff0000

def z134 : W := mkw 0x854df0000e4ad800 0x21537c000392b600 0xbf0ff0000c03fc03 0xafc3fc000300ff00

def z135 : W := mkw 0x4fffafbaac940098 0x53ffebeeab250026 0xdffffffff41c001f 0xf7fffffffd070007

def z136 : W := mkw 0x0000000500010504 0x0000000140004141 0xe001010f04031f1d 0xb8004043c100c7c7

def z137 : W := mkw 0x2066c6c8c3626260 0x0819b1b230d89898 0x00eecec0cbe0e0e2 0x403bb3b032f83838

def z138 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x1ff00ef00bfc00e2 0x47fc03bc02ff0038

def z139 : W := mkw 0xadfff6cccffbfb60 0x2b7ffdb333fefed8 0xfffffecccfffffe3 0xffffffb333fffff8

def z140 : W := mkw 0x144fa20fa001b524 0x4513e883e8006d49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z141 : W := mkw 0x044fa20aa0000000 0x4113e882a8000000 0x000e000000000000 0x0003800000000000

def z142 : W := mkw 0x099000000c900000 0x0264000003240000 0x1fe0000008e00002 0x07f8000002380000

def z143 : W := mkw 0x0609090200000000 0x0182424080000000 0x1f01010300000000 0x87c04040c0000000

def z144 : W := mkw 0x066f8f8a80000000 0x019be3e2a0000000 0xdfefcfcfc0000003 0xf7fbf3f3f0000000

def z145 : W := mkw 0xcf9939300c9c9898 0x33e64e4c03272626 0x1f113130041c1c1c 0x87c44c4c01070707

def z146 : W := mkw 0x4fffaffaadb402d8 0x53ffebfeab6d00b6 0x7ffe0ff00ffc03ff 0xdfff83fc03ff00ff

def z147 : W := mkw 0x3fffefefef63f7f4 0x4ffffbfbfbd8fdfd 0xffffffffffe3ffff 0xfffffffffff8ffff

def z148 : W := mkw 0x08f4f4f5f30f0f0e 0x423d3d3d7cc3c3c3 0xe0f1f1fff71f1f1d 0xf83c7c7ffdc7c7c7

def z149 : W := mkw 0x944ff20f024bfd24 0x2513fc83c092ff49 0x800ff00f0003fc00 0x2003fc03c000ff00

def z150 : W := mkw 0x2effefaee2436120 0x4bbffbebb890d848 0xdffffffff003e003 0xf7fffffffc00f800

def z151 : W := mkw 0x42205df5532f0fde 0x1088177d54cbc3f7 0xe011fffff71f1ffd 0xf8047ffffdc7c7ff

def z152 : W := mkw 0x8fffffffffdfdf0e 0x63fffffffff7f7c3 0xffffffffffffff1f 0xffffffffffffffc7

def z153 : W := mkw 0x170b4b4f4f03b7b4 0x05c2d2d3d3c0eded 0xff0fcfcfcf03ffff 0xffc3f3f3f3c0ffff

def z154 : W := mkw 0x8dfff6888edad800 0x237ffda223b6b600 0xfffffecccffffc03 0xffffffb333ffff00

def z155 : W := mkw 0x0e993933300c0c0e 0x43a64e4ccc030303 0x1f113133341c1c1c 0x87c44c4ccd070707

def z156 : W := mkw 0x499000500db402d8 0x12640014036d00b6 0x3ff000000ffc03ff 0xcffc000003ff00ff

def z157 : W := mkw 0x160b0b0f0001b5b4 0x0582c2c3c0006d6d 0xc00f0f0f0003fffc 0x3003c3c3c000ffff

def z158 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xc00ececcc003e3e0 0x3003b3b33000f8f8

def z159 : W := mkw 0x0020048000200040 0x0008012000080010 0x00e00e0008e000e2 0x0038038002380038

def z160 : W := mkw 0x0ab00da000000000 0x02ac036800000000 0xdff1fffff0000003 0xf7fc7ffffc000000

def z161 : W := mkw 0x0200092220000000 0x4080024888000000 0x0000013330000000 0x0000004ccc000000

def z162 : W := mkw 0x0002020aa0000000 0x40008082a8000000 0x0000000ff0000000 0x00000003fc000000

def z163 : W := mkw 0x030059555f0f0f9e 0x00c0165557c3c3e7 0xff11ffffff1f1fff 0xffc47fffffc7c7ff

def z164 : W := mkw 0x02668faaa0000000 0x4099a3eaa8000000 0xc0eecffff0000003 0x703bb3fffc000000

def z165 : W := mkw 0xa46ff6ccc36bfb60 0x291bfdb330dafed8 0xe0effecccbe3ffe3 0x783bffb332f8fff8

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000c0ccc0000001 0x7000303330000000

def z167 : W := mkw 0x4b9009200c900090 0x12e4024803240024 0x1f00000000000000 0x07c0000000000000

def z168 : W := mkw 0x0000001000040008 0x0000000400010002 0x00100130041c001c 0x8004004c01070007

def z169 : W := mkw 0x0effffaaa20a0800 0x43bfffeaa8828200 0xfffffffff71f1c03 0xfffffffffdc7c700

def z170 : W := mkw 0x8cddf000024ad800 0x23377c000092b600 0x9ffff0000003fc03 0xe7fffc000000ff00

def z171 : W := mkw 0x4effaffaa1b40248 0x53bfebfea86d0092 0xdffffffff3fc0003 0xf7fffffffcff0000

def z172 : W := mkw 0x170b0b0a0c00b0b0 0x05c2c2c283002c2c 0x1f0e0e000800e0e2 0x07c3838002003838

def z173 : W := mkw 0x48b004f001b40248 0x122c013c006d0092 0x60f001f007fc031d 0xd83c007c01ff00c7

def z174 : W := mkw 0x030009000c000090 0x00c0024003000024 0x1f0001000400001c 0x87c0004001000007

def z175 : W := mkw 0x9f9939030c989c94 0x27e64e40c3262725 0x1f113103041c1c1c 0x87c44c40c1070707

def z176 : W := mkw 0x2046c20cc2436120 0x0811b0833090d848 0x800ec00cc003e000 0x2003b0033000f800

def z177 : W := mkw 0x4b9009300c940098 0x12e4024c03250026 0x1f100130041c001c 0x87c4004c01070007

def z178 : W := mkw 0x170b5b5f5f0fbfbe 0x05c2d6d7d7c3efef 0xff1fffffff1fffff 0xffc7ffffffc7ffff

def z179 : W := mkw 0x170b0b0e0c01b1b0 0x05c2c2c383006c6c 0xff0e0e0c0803e3e3 0x3fc383830200f8f8

def z180 : W := mkw 0x2046820880406020 0x0811a08220101808 0x000e00000000e000 0x0003800000003800

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000e00080003e3 0x18000380020000f8

def z182 : W := mkw 0x099000000c900000 0x0264000003240000 0x3ff000000ffc0003 0xcffc000003ff0000

def z183 : W := mkw 0x610040544ff763f8 0x1840101513fdd8fe 0x200000000fffe3fc 0x0800000003fff8ff

def z184 : W := mkw 0x844df055534fdf0e 0x21137c1554d3f7c3 0xe01ff1fff71fff1d 0xf807fc7ffdc7ffc7

def z185 : W := mkw 0x8dddf0555fdfdf0e 0x23777c1557f7f7c3 0xfffff1ffffffff1f 0xfffffc7fffffffc7

def z186 : W := mkw 0x2066c68cc2636160 0x0819b1a33098d858 0x80eece0cc8e3e0e2 0x203bb3833238f838

def z187 : W := mkw 0x170b0b0a0c00b0b0 0x05c2c2c283002c2c 0x7f0e0f000c00e3ff 0x9fc383c0030038ff

def z188 : W := mkw 0x0022068880000000 0x000881a220000000 0x40000eccc0000000 0x100003b330000000

def z189 : W := mkw 0x02200da000000000 0x0088036800000000 0x40000ff000000000 0x100003fc00000000

def z190 : W := mkw 0x0e9b2b2a20000000 0x43a6caca88000000 0xdf1f3f3f30000003 0xb7c7cfcfcc000000

def z191 : W := mkw 0x064fab0aa0000000 0x4193eac2a8000000 0xdf0fff0ff0000003 0xb7c3ffc3fc000000

def z192 : W := mkw 0x4fffafaaacb000d0 0x53ffebeaab2c0034 0xdffffffff8e000e3 0xf7fffffffe380038

def z193 : W := mkw 0x006686c881200240 0x0019a1b220480090 0xe0eececccbe003e3 0x783bb3b332f800f8

def z194 : W := mkw 0x6bf4cdf0cff642d8 0x1afd337c33fd90b6 0x7ff0cff0cffc03ff 0xdffc33fc33ff00ff

def z195 : W := mkw 0xadfff6888efaf860 0x2b7ffda223bebe18 0xbffffe000ffffce3 0xefffff8003ffff38

def z196 : W := mkw 0x8000500002da4800 0x2000140000b69200 0x0000000003fc0000 0x0000000000ff0000

def z197 : W := mkw 0x9dddf0050edbfdb4 0x27777c0143b6ff6d 0xbffff0000fffffff 0xeffffc0003ffffff

def z198 : W := mkw 0x02220faaa0000000 0x408883eaa8000000 0x40000ffff0000000 0x100003fffc000000

def z199 : W := mkw 0xcfb93df00dbc9ad8 0x33ee4f7c036f26b6 0x7ff13ff00ffc1fff 0xdffc4ffc03ff07ff

def z200 : W := mkw 0x2046c20cc2436120 0x0811b0833090d848 0xa0eec00ccbe3e003 0x683bb00332f8f800

def z201 : W := mkw 0x2066868880606060 0x0819a1a220181818 0xc0eececcc8e0e0e3 0x703bb3b332383838

def z202 : W := mkw 0x2066868c80616160 0x0819a1a320185858 0xe0ee0e0c08e3e3e3 0x383b83830238f8f8

def z203 : W := mkw 0x8d9930111c9c9c0e 0x23664c0447272703 0x1f113133341c1c1c 0x87c44c4ccd070707

def z204 : W := mkw 0x060b0b0e00012120 0x0182c2c380004848 0xff0f0f0f0803e3e3 0xbfc3c3c3c200f8f8

def z205 : W := mkw 0x000000505104020a 0x0000001414410082 0x000000f0f0000000 0x0000003c3c000000

def z206 : W := mkw 0x170b0b5f5d05b7be 0x05c2c2d7d7416def 0xff0f0ffffc03ffff 0xbfc3c3ffff00ffff

def z207 : W := mkw 0x08f4a4a0a0000000 0x423d292828000000 0x00f0f0f0f0000000 0x403c3c3c3c000000

def z208 : W := mkw 0x48b004f001b40248 0x122c013c006d0092 0x00f000f003fc0000 0x403c003c00ff0000

def z209 : W := mkw 0x88d4f00002da4800 0x22353c0000b69200 0x00f0f00003fc0000 0x403c3c0000ff0000

def z210 : W := mkw 0x6bf6cffccff763f8 0x1afdb3ff33fdd8fe 0xfffecffccfffe3ff 0xffffb3ff33fff8ff

def z211 : W := mkw 0x310040454f63f7f4 0x0c40101153d8fdfd 0x200000000fe3fffc 0x0800000003f8ffff

def z212 : W := mkw 0x000040555307070e 0x0000101554c1c1c3 0xe000c1fff303031d 0x7800307ffcc0c0c7

def z213 : W := mkw 0x0effefeee3030300 0x43bffbfbb8c0c0c0 0xfffffffff3030303 0xfffffffffcc0c0c0

def z214 : W := mkw 0x4b9009700d940298 0x12e4025c036500a6 0x7f1001f0071c031d 0xdfc4007c01c700c7

def z215 : W := mkw 0x170909030c009494 0x05c24240c3002525 0x7f010f030c001fff 0x9fc043c0c30007ff

def z216 : W := mkw 0xa8f4f4c0c3fa4a40 0x2a3d3d3030fe9290 0x00f0f0c0c3fc0000 0x403c3c3030ff0000

def z217 : W := mkw 0x8dddf0505fdeda0a 0x23777c1417f7b682 0xbffff0f0fffffc03 0xeffffc3c3fffff00

def z218 : W := mkw 0x430009500db402d8 0x10c00254036d00b6 0x7f000f000ffc03ff 0x9fc003c003ff00ff

def z219 : W := mkw 0x2046c20cc2436120 0x0811b0833090d848 0xe00ece0cc803e3e3 0x3803b3833200f8f8

def z220 : W := mkw 0x4fffffffffbf0fde 0x53ffffffffefc3f7 0xffffffffffff1fff 0xffffffffffffc7ff

def z221 : W := mkw 0x0000000500010504 0x0000000140004141 0x4000010f0000031c 0x10000043c00000c7

def z222 : W := mkw 0x0000404443030300 0x0000101110c0c0c0 0xe000c0ccc3030301 0x7800303330c0c0c0

def z223 : W := mkw 0x060b5b5f530f0f0e 0x0182d6d7d4c3c3c3 0xff1ffffff71f1f1f 0xffc7fffffdc7c7c7

def z224 : W := mkw 0xcdddf0500ffedad8 0x33777c1403ffb6b6 0xbffff0000fffffff 0xeffffc0003ffffff

def z225 : W := mkw 0x376f8f8a8c60f0f0 0x0ddbe3e2a3183c3c 0x1fee0e0008e0e0e2 0x07fb838002383838

def z226 : W := mkw 0x9f9b3b0f0c99bdb4 0x27e6cec3c3266f6d 0xff1f3f0f0c1fffff 0xbfc7cfc3c307ffff

def z227 : W := mkw 0x1fffafafac01b5b4 0x47ffebebeb006d6d 0xfffffffffc03ffff 0xffffffffff00ffff

def z228 : W := mkw 0x08d4a00000000000 0x0235280000000000 0x00f0f00000000000 0x403c3c0000000000

def z229 : W := mkw 0x2064d4d5d36f4f4e 0x0819353574dbd3d3 0xe0f1f1fff7ff1f1d 0xf83c7c7ffdffc7c7

def z230 : W := mkw 0xa10050444ffbfb60 0x2840141113fefed8 0x200000000fffffe0 0x0800000003fffff8

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x401001f000000001 0xd004007c00000000

def z232 : W := mkw 0x376fcfcfcf63f7f4 0x0ddbf3f3f3d8fdfd 0xffefcfcfcfe3ffff 0xfffbf3f3f3f8ffff

def z233 : W := mkw 0x2066c6dcc3676368 0x0819b1b730d9d8da 0xe0fecffccfffe3ff 0xf83fb3ff33fff8ff

def z234 : W := mkw 0x48b054f053be0a4a 0x122c153c14ef8292 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z235 : W := mkw 0x206686ccc1616360 0x0819a1b3305858d8 0x40ee0eccc8e0e3e2 0x103b83b3323838f8

def z236 : W := mkw 0x00005000020a0800 0x0000140000828200 0xe011f1fff71f1c01 0xf8047c7ffdc7c700

def z237 : W := mkw 0x12020b0f000125b4 0x048082c3c000496d 0x40000f0f000003fc 0x100003c3c00000ff

def z238 : W := mkw 0x00005005020b0d04 0x000014014082c341 0xe011f10f071f1f1d 0xf8047c43c1c7c7c7

def z239 : W := mkw 0x2effafaaa0606060 0x4bbfebeaa8181818 0xdffffffff8e0e0e3 0xf7fffffffe383838

def z240 : W := mkw 0x2effafaaa0606060 0x4bbfebeaa8181818 0x1fee0e0008e0e0e2 0x07fb838002383838

def z241 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xfffff1fffffffc03 0xfffffc7fffffff00

def z242 : W := mkw 0x5fbb0faf0cb1b5f4 0x17eec3ebc32c6d7d 0xffef0f0f0ce3ffff 0xbffbc3c3c338ffff

def z243 : W := mkw 0x0409200220000000 0x4102480088000000 0x0001300330000000 0x00004c00cc000000

def z244 : W := mkw 0x046fa68aa0000000 0x411be9a2a8000000 0xc0effecff0000003 0x703bffb3fc000000

def z245 : W := mkw 0xc8f4f4f003fe4a48 0x323d3d3c00ff9292 0x00f0f0f003fc0000 0x403c3c3c00ff0000

def z246 : W := mkw 0x0000000400010100 0x0000000100004040 0xe000000c00030301 0x380000030000c0c0

def z247 : W := mkw 0xcffdadf00df4d2d8 0x33ff6b7c037d34b6 0x7ffe0ff00ffce3ff 0xdfff83fc03ff38ff

def z248 : W := mkw 0x4bf68ff88db402d8 0x12fda3fe236d00b6 0xfffecffccffc03ff 0xffffb3ff33ff00ff

def z249 : W := mkw 0x9fdfab0a0cd0f0b0 0x27f7eac283343c2c 0x1fee0e0008e0e0e2 0x07fb838002383838

def z250 : W := mkw 0x2366cfcccf6363f0 0x08d9b3f333d8d8fc 0xffeecfcccfe3e3ff 0xfffbb3f333f8f8ff

def z251 : W := mkw 0x3266cfcfc36367f4 0x0c99b3f3f0d8d9fd 0xe0eecfcfcbe3e3ff 0x783bb3f3f2f8f8ff

def z252 : W := mkw 0x2066c6ddd367676e 0x0819b1b774d9d9db 0xe0eecffffbe3e3ff 0x783bb3fffef8f8ff

def z253 : W := mkw 0x844da0000040d000 0x2113680000103400 0x000e00000000e000 0x0003800000003800

def z254 : W := mkw 0x0edfab0a00000000 0x03b7eac280000000 0xdfffff0f00000003 0xf7ffffc3c0000000

def z255 : W := mkw 0x4bb05df00fbe0ad8 0x12ec177c03ef82b6 0xfff1fff00fff1fff 0xfffc7ffc03ffc7ff

def z256 : W := mkw 0x1fffafaaac00b0b0 0x47ffebeaab002c2c 0x1fee0e000800e0e2 0x07fb838002003838

def z257 : W := mkw 0x060b0b0a00000000 0x0182c2c280000000 0xdf1ffffff0000003 0xf7c7fffffc000000

def z258 : W := mkw 0x0002020d00012524 0x0000808340004949 0xe00f0f0f0c03ffff 0xb803c3c3c300ffff

def z259 : W := mkw 0x00005045530b0f06 0x0000141154c2c3c1 0xe001f0cff3031f01 0x78007c33fcc0c7c0

def z260 : W := mkw 0x00001055510d0f0e 0x00000415544343c3 0x401131fff41c1f1c 0x90044c7ffd0707c7

def z261 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0fffffffbe3e3e3 0xf83ffffffef8f8f8

def z262 : W := mkw 0x6bf68ff88df462f8 0x1afda3fe237d18be 0x7ffe0ff00ffce3ff 0xdfff83fc03ff38ff

def z263 : W := mkw 0x2066d6cdd36b6f66 0x0819b5b374dadbd9 0xe0effecffbe3ffe3 0x783bffb3fef8fff8

def z264 : W := mkw 0x244fe20ee2436120 0x4913f883b890d848 0x800ff00ff003e000 0x2003fc03fc00f800

def z265 : W := mkw 0x2000400442436120 0x080010011090d848 0x000000000003e000 0x000000000000f800

def z266 : W := mkw 0x844ff20aa24ad800 0x6113fc82a892b600 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z267 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x1ff001f007fc001c 0xc7fc007c01ff0007

def z268 : W := mkw 0x4bb00de00db002d0 0x12ec0378036c00b4 0x7fe00ec00be003e3 0x5ff803b002f800f8

def z269 : W := mkw 0x8fdffb0a0edad800 0x23f7fec283b6b600 0xffffff0f0ffffc03 0xffffffc3c3ffff00

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0x8011f00000000001 0xe0047c0000000000

def z271 : W := mkw 0xadffe6cccff3f360 0x2b7ff9b333fcfcd8 0xffeececccbe3e3e3 0x7ffbb3b332f8f8f8

def z272 : W := mkw 0x2266cfeee3636360 0x4899b3fbb8d8d8d8 0xe0eecffffbe3e3e3 0x783bb3fffef8f8f8

def z273 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0eececccfffffff 0x783bb3b333ffffff

def z274 : W := mkw 0x00005000020a0800 0x0000140000828200 0xa011f000071f1c01 0xe8047c0001c7c700

def z275 : W := mkw 0x246fe6cee3636360 0x491bf9b3b8d8d8d8 0xe0effecffbe3e3e3 0x783bffb3fef8f8f8

def z276 : W := mkw 0x410050555fbf0fde 0x1040141557efc3f7 0xe011f1ffffff1ffd 0xf8047c7fffffc7ff

def z277 : W := mkw 0x4890003000940008 0x1224000c00250002 0x00100030001c0000 0x0004000c00070000

def z278 : W := mkw 0x88d4f00002da4800 0x22353c0000b69200 0xa0fef0000bffe003 0x683fbc0002fff800

def z279 : W := mkw 0x8144d0000edad800 0x2051340003b6b600 0xa0eec0000ffffc03 0x683bb00003ffff00

def z280 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x1fee0e0000000002 0x07fb838000000000

def z281 : W := mkw 0x0000000500010504 0x0000000140004141 0x8001000f00031c00 0x20004003c000c700

def z282 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x9feffe0ff0000002 0x27fbff83fc000000

def z283 : W := mkw 0x48b004f001b40248 0x122c013c006d0092 0x60f00ef00bfc03e3 0x583c03bc02ff00f8

def z284 : W := mkw 0x0a90092000000000 0x02a4024800000000 0x1f10013000000000 0x87c4004c00000000

def z285 : W := mkw 0x2efffffff36f6f6e 0x4bbffffffcdbdbdb 0xffffffffffffffff 0xffffffffffffffff

def z286 : W := mkw 0x0002020800002020 0x0000808200000808 0x000e0e000800e0e2 0x0003838002003838

def z287 : W := mkw 0x4fffafaaacb000d0 0x53ffebeaab2c0034 0x1fee0e0008e000e2 0x07fb838002380038

def z288 : W := mkw 0x050950555f0f9f0e 0x0142541557c3e7c3 0xff1ff1ffff1fff1f 0xffc7fc7fffc7ffc7

def z289 : W := mkw 0x0cdda00000000000 0x0337680000000000 0xdffff1fff0000003 0xf7fffc7ffc000000

def z290 : W := mkw 0x4bb00da00cb000d0 0x12ec0368032c0034 0x3ff00e000ffc00e3 0xcffc038003ff0038

def z291 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x2010f0f0f71f1f1c 0x48043c3c3dc7c7c7

def z292 : W := mkw 0x0000005001040208 0x0000001400410082 0x400001f00000031c 0x1000007c000000c7

def z293 : W := mkw 0x130009050c01b5b4 0x04c0024143006d6d 0x7f000f000c03ffff 0x9fc003c00300ffff

def z294 : W := mkw 0x970b5b0f0edbfdb4 0x25c2d6c3c3b6ff6d 0xff0f0f0f0fffffff 0xbfc3c3c3c3ffffff

def z295 : W := mkw 0x0044d055534f4f0e 0x0011341554d3d3c3 0xe0fff1ffffffff1f 0xf83ffc7fffffffc7

def z296 : W := mkw 0x050950000e0a9800 0x014254000382a600 0xbf1ff0000f1ffc03 0xefc7fc0003c7ff00

def z297 : W := mkw 0x000000111004040e 0x0000000444010103 0x000001333000001c 0x0000004ccc000007

def z298 : W := mkw 0x2000004441212360 0x08000011104848d8 0x00000000000003e0 0x00000000000000f8

def z299 : W := mkw 0x8dfdf4c00ffada40 0x237f7d3003feb690 0xfffffec00fffffe3 0xffffffb003fffff8

def z300 : W := mkw 0x12020b0f000125b4 0x048082c3c000496d 0xe00e0f0f0803e3ff 0x380383c3c200f8ff

def z301 : W := mkw 0x844df005524bdd06 0x21137c015492f741 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z302 : W := mkw 0x206686ccc1212360 0x0819a1b3304848d8 0xc0eececcc00003e3 0x703bb3b3300000f8

def z303 : W := mkw 0xeffffffccffffbf8 0x3bffffff33fffefe 0xfffffffccfffffff 0xffffffff33ffffff

def z304 : W := mkw 0x172b0fcf0d21b7f4 0x05cac3f3c3486dfd 0xffef0fcf0fe3ffff 0xfffbc3f3c3f8ffff

def z305 : W := mkw 0x4b9019311c9c0c9e 0x12e4064c47270327 0x1f113133341c1c1c 0x87c44c4ccd070707

def z306 : W := mkw 0x00001011100c0c0e 0x0000040444030303 0xc011f1fff41c1c1d 0xf0047c7ffd070707

def z307 : W := mkw 0x002004c001200240 0x0008013000480090 0x00e000c003e00000 0x4038003000f80000

def z308 : W := mkw 0x8ddda0000cd0d000 0x2377680003343400 0x3ffe00000ffce003 0xcfff800003ff3800

def z309 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x5f0e0f0f0800e3fe 0x17c383c3c20038ff

def z310 : W := mkw 0x010000000c000090 0x0040000003000024 0x200000000c0003fc 0x08000000030000ff

def z311 : W := mkw 0x170b0b5f0d05b7bc 0x05c2c2d7c3416def 0xff1f0fff0f1fffff 0xffc7c3ffc3c7ffff

def z312 : W := mkw 0x49b004f00db40248 0x126c013c036d0092 0x3ff000f00ffc0003 0xcffc003c03ff0000

def z313 : W := mkw 0x170b5b5f5f0fbfbe 0x05c2d6d7d7c3efef 0xff0f0f0f0f1fffff 0xbfc3c3c3c3c7ffff

def z314 : W := mkw 0x0890000000000000 0x0224000000000000 0x1ff0000000000003 0xc7fc000000000000

def z315 : W := mkw 0x8890300000980800 0x22240c0000260200 0x00103000001c0000 0x00040c0000070000

def z316 : W := mkw 0x0046c20c02436120 0x0011b0830090d848 0xe0eece0c0be3e3e3 0x783bb38302f8f8f8

def z317 : W := mkw 0xadffa6888cf0f060 0x2b7fe9a2233c3c18 0x1fee0e0008e0e0e2 0x07fb838002383838

def z318 : W := mkw 0x08f4f4f0f30e0a0a 0x423d3d3c3cc38282 0x00f0f0f0f31c0000 0x403c3c3c3cc70000

def z319 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x1ffef0000bfce002 0x47ffbc0002ff3800

def z320 : W := mkw 0x810010000c989800 0x2040040003262600 0x00000000041c1c00 0x0000000001070700

def z321 : W := mkw 0x5f9909330c94949c 0x17e6424cc3252527 0x1f110133041c1c1c 0x87c4404cc1070707

def z322 : W := mkw 0x202044c443636360 0x0808113110d8d8d8 0x60e00ec00be3e3e3 0x583803b002f8f8f8

def z323 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x4010f1fff31c031c 0x50043c7ffcc700c7

def z324 : W := mkw 0x0200090000000090 0x0080024000000024 0x40000f00000003fc 0x100003c0000000ff

def z325 : W := mkw 0xcffdada00cf0d0d0 0x33ff6b68033c3434 0x1fee0e0008e0e0e2 0x07fb838002383838

def z326 : W := mkw 0x08b004a000000000 0x022c012800000000 0x00f000f000000000 0x403c003c00000000

def z327 : W := mkw 0x0bb00da00c900000 0x02ec036803240000 0x7ff00ff00ffc0003 0xdffc03fc03ff0000

def z328 : W := mkw 0x7fffcfffcff7f7fc 0x1ffff3fff3fdfdff 0xffffcfffcfffffff 0xfffff3fff3ffffff

def z329 : W := mkw 0x510000550db5b7fc 0x14400015436d6dff 0x200000000ffffffc 0x0800000003ffffff

def z330 : W := mkw 0x2046d20dd24b6d26 0x0811b4837492db49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z331 : W := mkw 0x170909070c019594 0x05c24241c3006565 0xff01010f04031f1d 0xbfc04043c100c7c7

def z332 : W := mkw 0x070b0b0a0c000090 0x01c2c2c283000024 0xff0f0f0f0c0003ff 0xbfc3c3c3c30000ff

def z333 : W := mkw 0x43200df00d2402d8 0x10c8037c034900b6 0x7f000ff00c0003ff 0x9fc003fc030000ff

def z334 : W := mkw 0x2046d25dd34f6f2e 0x0811b49774d3dbcb 0xe01ff1fff71fff1d 0xf807fc7ffdc7ffc7

def z335 : W := mkw 0x376fdfdfdf6ffffe 0x0ddbf7f7f7dbffff 0xffffffffffffffff 0xffffffffffffffff

def z336 : W := mkw 0x2066d6dcd36f6b6a 0x0819b5b734dbdada 0xe0fefefcfbffe3e3 0x783fbfbf3efff8f8

def z337 : W := mkw 0x0c99200000000000 0x0326480000000000 0x1f11300000000000 0x87c44c0000000000

def z338 : W := mkw 0x00005005520b0d06 0x000014015482c341 0xa011f00ff71f1c01 0xe8047c03fdc7c700

def z339 : W := mkw 0x0000000000000000 0x0000000000000000 0xc001010f00000001 0xb0004043c0000000

def z340 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x3fee00000ffffc02 0x0ffb800003ffff00

def z341 : W := mkw 0x1fffafafac01b5b4 0x47ffebebeb006d6d 0xffef0f0f0c03ffff 0xbffbc3c3c300ffff

def z342 : W := mkw 0x0effefaaa2424000 0x43bffbeaa8909000 0xfffffffffbe3e003 0xfffffffffef8f800

def z343 : W := mkw 0x0effafafa0010504 0x43bfebebe8004141 0xfffffffff4031f1f 0xfffffffffd00c7c7

def z344 : W := mkw 0x9fdfab0f0cd1f5b4 0x27f7eac3c3347d6d 0xffef0f0f0ce3ffff 0xbffbc3c3c338ffff

def z345 : W := mkw 0x0000000400012120 0x0000000100004848 0x200000000803e3e0 0x080000000200f8f8

def z346 : W := mkw 0x2064c4c0c3624240 0x0819313030d89090 0x60e0cec0cbe003e3 0x583833b032f800f8

def z347 : W := mkw 0x9fdffb5f5fdfffbe 0x27f7fed7d7f7ffef 0xffffffffffffffff 0xffffffffffffffff

def z348 : W := mkw 0x0890202020000000 0x4224080808000000 0x0010303030000000 0x00040c0c0c000000

def z349 : W := mkw 0x010000000c000000 0x0040000003000000 0x3f0000000c000003 0x8fc0000003000000

def z350 : W := mkw 0x00005050530e0a0a 0x0000141414c38282 0x6010f1f0f71c031d 0xd8043c7c3dc700c7

def z351 : W := mkw 0x5bb20fff0db527fc 0x16ec83ffc36d49ff 0x7ff00fff0ffc03ff 0xdffc03ffc3ff00ff

def z352 : W := mkw 0xaddff20ccedbf920 0x2b77fc8333b6fe48 0xbffff00ccffffc03 0xeffffc0333ffff00

def z353 : W := mkw 0x810050555fdfdf0e 0x2040141557f7f7c3 0x200000000fffff1c 0x0800000003ffffc7

def z354 : W := mkw 0x0ebb0faa00000000 0x03aec3ea80000000 0xdfff0fff00000003 0xf7ffc3ffc0000000

def z355 : W := mkw 0x8effffaaa24ad800 0x63bfffeaa892b600 0xdffffffff003fc03 0xf7fffffffc00ff00

def z356 : W := mkw 0x060b0b0f00010504 0x0182c2c3c0004141 0xff0f0f0f04031f1f 0xbfc3c3c3c100c7c7

def z357 : W := mkw 0x810050000edad800 0x2040140003b6b600 0xa011f0000ffffc01 0xe8047c0003ffff00

def z358 : W := mkw 0x044da00000000000 0x0113680000000000 0x800ff00000000000 0x2003fc0000000000

def z359 : W := mkw 0x8fffffaaaedad800 0x63ffffeaabb6b600 0xbffffe000ffffc03 0xefffff8003ffff00

def z360 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x600001fff71f1f1c 0x1800007ffdc7c7c7

def z361 : W := mkw 0x0200090000000000 0x0080024000000000 0x5f000f0000000003 0x97c003c000000000

def z362 : W := mkw 0x4bb20ffaadb402d8 0x52ec83feab6d00b6 0x7ff00ffffffc03ff 0xdffc03ffffff00ff

def z363 : W := mkw 0x1002020f00012524 0x04008083c0004949 0x0000000f00000000 0x00000003c0000000

def z364 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x3fe00e000ffc03fe 0x0ff8038003ff00ff

def z365 : W := mkw 0x0000400002020000 0x0000100000808000 0xa000c00003030001 0x6800300000c0c000

def z366 : W := mkw 0x8d9930000c989800 0x23664c0003262600 0xbf1f30000c1ffc03 0xafc7cc000307ff00

def z367 : W := mkw 0x42220ffaa12402d8 0x508883fea84900b6 0x40000ffff00003fc 0x100003fffc0000ff

def z368 : W := mkw 0x160b0b0f000125b4 0x0582c2c3c000496d 0xdf0f0f0f000003ff 0xb7c3c3c3c00000ff

def z369 : W := mkw 0x8dddf0500fdeda08 0x23777c1403f7b682 0xfffff1f00fffff1f 0xfffffc7c03ffffc7

def z370 : W := mkw 0x0044c04443434300 0x0011301110d0d0c0 0xe0eec0cccbe3e303 0x783bb03332f8f8c0

def z371 : W := mkw 0x140b525f530fbf2e 0x0502d497d4c3efcb 0xe01ff1fff71fff1d 0xf807fc7ffdc7ffc7

def z372 : W := mkw 0x2066c6cdc3636764 0x0819b1b370d8d9d9 0xe0efcfcfcfe3ffff 0xf83bf3f3f3f8ffff

def z373 : W := mkw 0x12020b5f510527be 0x048082d7d44149ef 0x40000ffff00003fc 0x100003fffc0000ff

def z374 : W := mkw 0x150b020f0c01b5b4 0x0542c083c3006d6d 0xa00f000f0c03fffc 0x2803c003c300ffff

def z375 : W := mkw 0x202256ddd32f2f6e 0x080895b774cbcbdb 0xe011fffff71f1ffd 0xf8047ffffdc7c7ff

def z376 : W := mkw 0x1f9b2b2f2c01b5b4 0x47e6cacbcb006d6d 0xff1f3f3f3c03ffff 0xbfc7cfcfcf00ffff

def z377 : W := mkw 0x8f9939222c989800 0x63e64e488b262600 0x1f113133341c1c00 0x87c44c4ccd070700

def z378 : W := mkw 0x4ab00df0012402d8 0x12ac037c004900b6 0x5ff00ff0000003ff 0xd7fc03fc000000ff

def z379 : W := mkw 0x174fcb0f0e43f5b4 0x05d3f2c3c390fd6d 0xffefcf0f0fe3ffff 0xfffbf3c3c3f8ffff

def z380 : W := mkw 0x12220fafa00125b4 0x448883ebe800496d 0x40000ffff00003fc 0x100003fffc0000ff

def z381 : W := mkw 0x3166c6cdcf63f7f4 0x0c59b1b373d8fdfd 0xe0eececccfe3ffff 0x783bb3b333f8ffff

def z382 : W := mkw 0x02225ffff30f0f0e 0x408897fffcc3c3c3 0xe011fffff71f1f1d 0xf8047ffffdc7c7c7

def z383 : W := mkw 0x00005051530e0e0e 0x0000141454c38383 0x0011f1f3f71c1c1c 0xc0047c7cfdc70707

def z384 : W := mkw 0x8409300000089800 0x21024c0000022600 0x0001300000001c00 0x00004c0000000700

def z385 : W := mkw 0x372b0fcfcd21b7f4 0x0dcac3f3f3486dfd 0xff0f0fcfcc03ffff 0xbfc3c3f3f300ffff

def z386 : W := mkw 0x6166c6dccff763f8 0x1859b1b733fdd8fe 0xe0eececccfffe3ff 0x783bb3b333fff8ff

def z387 : W := mkw 0x0b9009000c900090 0x02e4024003240024 0x7ff00f000ffc03ff 0xdffc03c003ff00ff

def z388 : W := mkw 0x0effaffaa1040208 0x43bfebfea8410082 0xfffffffff71c031f 0xfffffffffdc700c7

def z389 : W := mkw 0x000000555105070e 0x00000015544141c3 0x000000000000031c 0x00000000000000c7

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00e00000803e003 0x280380000200f800

def z391 : W := mkw 0x202004c0c1200240 0x0808013030480090 0x000000c0c0000000 0x0000003030000000

def z392 : W := mkw 0x030009500d040298 0x00c00254034100a6 0x7f100ff00f1c03ff 0xdfc403fc03c700ff

def z393 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xa001f00ff71f1f1c 0x28007c03fdc7c7c7

def z394 : W := mkw 0x4fb90df00db492d8 0x13ee437c036d24b6 0xffff0ff00fffffff 0xffffc3fc03ffffff

def z395 : W := mkw 0x1fffffffff0fbfbe 0x47ffffffffc3efef 0xffffffffff1fffff 0xffffffffffc7ffff

def z396 : W := mkw 0x4bb00df55db507de 0x12ec037d576d41f7 0x7ff00ffffffc03ff 0xdffc03ffffff00ff

def z397 : W := mkw 0x054dc0000e42d000 0x015370000390b400 0xbfefc0000fe3fc03 0xeffbf00003f8ff00

def z398 : W := mkw 0x2064c4c4c3636360 0x0819313130d8d8d8 0x20e0c0c0cbe3e3e0 0x4838303032f8f8f8

def z399 : W := mkw 0xcbb05df00ffedad8 0x32ec177c03ffb6b6 0x7ff00ff00fffffff 0xdffc03fc03ffffff

def z400 : W := mkw 0x00005050530e0a0a 0x0000141414c38282 0xa011f0f0f71f1c01 0xe8047c3c3dc7c700

def z401 : W := mkw 0x0020048000000000 0x0008012000000000 0x40e00ec000000003 0x503803b000000000

def z402 : W := mkw 0x044ff25ff30f0f0e 0x4113fc97fcc3c3c3 0xe01ff1fff71f1f1d 0xf807fc7ffdc7c7c7

def z403 : W := mkw 0x174fab0fac01b5b4 0x45d3eac3eb006d6d 0xff0fff0ffc03ffff 0xbfc3ffc3ff00ffff

def z404 : W := mkw 0x0effafaea0012120 0x43bfebeba8004848 0xfffffffff803e3e3 0xfffffffffe00f8f8

def z405 : W := mkw 0x099050555f9f0f0e 0x0264141557e7c3c3 0xfff1f1ffffff1f1f 0xfffc7c7fffffc7c7

def z406 : W := mkw 0x48b004a000b00040 0x122c0128002c0010 0x00e0000000e00000 0x0038000000380000

def z407 : W := mkw 0x0000005001040208 0x0000001400410082 0xe011f1fff71c031d 0xf8047c7ffdc700c7

def z408 : W := mkw 0x0000100000080800 0x0000040000020200 0x00113000041c1c00 0x80044c0001070700

def z409 : W := mkw 0x099050000e9a0800 0x0264140003a68200 0xbff1f0000fff1c03 0xeffc7c0003ffc700

def z410 : W := mkw 0x346fc6cfc363f764 0x0d1bf1b3f0d8fdd9 0xe0efcecfcbe3ffe3 0x783bf3b3f2f8fff8

def z411 : W := mkw 0x256fc6cccf63f360 0x095bf1b333d8fcd8 0xffefcecccfe3ffe3 0xfffbf3b333f8fff8

def z412 : W := mkw 0x8fddf9222edad800 0x63f77e488bb6b600 0xbffff1333ffffc03 0xeffffc4ccfffff00

def z413 : W := mkw 0xcdfdf4f00ffeda48 0x337f7d3c03ffb692 0xbffff0f00ffffc03 0xeffffc3c03ffff00

def z414 : W := mkw 0x110050555f0fbfbe 0x0440141557c3efef 0xe011f1ffff1ffffd 0xf8047c7fffc7ffff

def z415 : W := mkw 0x8dddf0555fdfdf0e 0x23777c1557f7f7c3 0xbffff0000fffff1f 0xeffffc0003ffffc7

def z416 : W := mkw 0xcffdfdf55fffdfde 0x33ff7f7d57fff7f7 0xffffffffffffffff 0xffffffffffffffff

def z417 : W := mkw 0x0effffaff20b0d06 0x43bfffebfc82c341 0xdffffffff0031c03 0xf7fffffffc00c700

def z418 : W := mkw 0x8d9970000edad800 0x23665c0003b6b600 0x3f1130000ffffc00 0x8fc44c0003ffff00

def z419 : W := mkw 0x099000000c900000 0x0264000003240000 0x1f100000041c0000 0x87c4000001070000

def z420 : W := mkw 0xa166d6cccffbfb60 0x2859b5b333fefed8 0xe0eececccfffffe3 0x783bb3b333fffff8

def z421 : W := mkw 0x8d9930000c989800 0x23664c0003262600 0x3ff130000ffc1c03 0xcffc4c0003ff0700

def z422 : W := mkw 0x850950000edad800 0x2142540003b6b600 0xbf0f00000ffffc03 0xafc3c00003ffff00

def z423 : W := mkw 0x00005050530e0a0a 0x0000141414c38282 0xc011f1fff31c0001 0xf0047c7ffcc70000

def z424 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x20113133371f1f1c 0x88044c4ccdc7c7c7

def z425 : W := mkw 0x42200df0012402d8 0x1088037c004900b6 0x60e00ff00be003ff 0x583803fc02f800ff

def z426 : W := mkw 0x0409000000000000 0x0102400000000000 0x9f0f000000000003 0xa7c3c00000000000

def z427 : W := mkw 0x0002020c00012120 0x0000808300004848 0x800e000c0003e000 0x200380030000f800

def z428 : W := mkw 0x0effafeaa1200240 0x43bfebfaa8480090 0xfffffffffbe003e3 0xfffffffffef800f8

def z429 : W := mkw 0x202206ccc1212360 0x080881b3304848d8 0x60e00ecccbe003e3 0x583803b332f800f8

def z430 : W := mkw 0x0ab00da000000000 0x02ac036800000000 0x1fe00e0000000002 0x07f8038000000000

def z431 : W := mkw 0x00005005520b0d06 0x000014015482c341 0xc011f1fff0031c01 0xf0047c7ffc00c700

def z432 : W := mkw 0x89d4f0000edad800 0x22753c0003b6b600 0x20f0f0000ffffc00 0x483c3c0003ffff00

def z433 : W := mkw 0x1f9929232c009494 0x47e64a48cb002525 0x1f11313334001c1c 0x87c44c4ccd000707

def z434 : W := mkw 0x170959575f0f9f9e 0x05c25655d7c3e7e7 0xff11f1fff71f1f1d 0xffc47c7ffdc7c7c7

def z435 : W := mkw 0x1effafafa00125b4 0x47bfebebe800496d 0xdffffffff00003ff 0xf7fffffffc0000ff

def z436 : W := mkw 0x6bf6dffddfff6ffe 0x1afdb7ff77ffdbff 0xffffffffffffffff 0xffffffffffffffff

def z437 : W := mkw 0x2066c68cc2436120 0x0819b1a33090d848 0xc0eececcc003e003 0x703bb3b33000f800

def z438 : W := mkw 0x0effaffff105070e 0x43bfebfffc4141c3 0xdffffffff000031f 0xf7fffffffc0000c7

def z439 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x9f1ff000041ffc00 0xa7c7fc000107ff00

def z440 : W := mkw 0x8d9970000e9a9800 0x23665c0003a6a600 0xbf11f000071f1c01 0xefc47c0001c7c700

def z441 : W := mkw 0x8dddb0000c989800 0x23776c0003262600 0x9ffff000041c1c03 0xe7fffc0001070700

def z442 : W := mkw 0x2066d6ccc36b6b60 0x0819b5b330dadad8 0xe0fffecccfffffe3 0xf83fffb333fffff8

def z443 : W := mkw 0x0000400442030100 0x000010011080c040 0x8000c00cc0030000 0x200030033000c000

def z444 : W := mkw 0x266fcfcec3636360 0x099bf3f3b0d8d8d8 0xffefcfcfcbe3e3e3 0xfffbf3f3f2f8f8f8

def z445 : W := mkw 0x28f6e6ece3636360 0x4a3db9bb38d8d8d8 0xe0fefefcfbe3e3e3 0x783fbfbf3ef8f8f8

def z446 : W := mkw 0x6bb04df44ff763f8 0x1aec137d13fdd8fe 0x7ff00ff00fffe3ff 0xdffc03fc03fff8ff

def z447 : W := mkw 0x4bb00db00c940098 0x12ec036c03250026 0x5ff00ff0041c001f 0xd7fc03fc01070007

def z448 : W := mkw 0xadddf0444ffbfb60 0x2b777c1113fefed8 0xbffff0000fffffe3 0xeffffc0003fffff8

def z449 : W := mkw 0x40000050012402d8 0x10000014004900b6 0x00000000000003fc 0x00000000000000ff

def z450 : W := mkw 0x4ffdadf00db402d8 0x13ff6b7c036d00b6 0xfffffff00ffc03ff 0xfffffffc03ff00ff

def z451 : W := mkw 0x2effefeae3624240 0x4bbffbfab8d89090 0xdffffffff3e00003 0xf7fffffffcf80000

def z452 : W := mkw 0x00005005520b0d06 0x000014015482c341 0xe001f10ff4031f1d 0xb8007c43fd00c7c7

def z453 : W := mkw 0x376fcfcecf63f3f0 0x0ddbf3f3b3d8fcfc 0xffeececccbe3e3e3 0x7ffbb3b332f8f8f8

def z454 : W := mkw 0x0efdada2a0000000 0x43bf6b68a8000000 0x1ff1f1f3f0000000 0xc7fc7c7cfc000000

def z455 : W := mkw 0x2044c000c2424000 0x0811300030909000 0x0000c000c0000000 0x0000300030000000

def z456 : W := mkw 0x0cdda00000000000 0x0337680000000000 0x1fee000000000002 0x07fb800000000000

def z457 : W := mkw 0x00005000020a0800 0x0000140000828200 0x0010f000031c0000 0x40043c0000c70000

def z458 : W := mkw 0x02020b0a00000000 0x008082c280000000 0x40000f0f00000000 0x100003c3c0000000

def z459 : W := mkw 0x0efffffaf30e0a0a 0x43bffffebcc38282 0xdffffffff31c0003 0xf7fffffffcc70000

def z460 : W := mkw 0x8dddf0055edbdd06 0x23777c0157b6f741 0xbffff00ffffffc03 0xeffffc03ffffff00

def z461 : W := mkw 0x2064c4c4c3634340 0x0819313130d8d0d0 0xe0e0c0ccc3e30301 0x7838303330f8c0c0

def z462 : W := mkw 0x88d4f00002da4800 0x22353c0000b69200 0xa0f1f00007ff1c01 0xe83c7c0001ffc700

def z463 : W := mkw 0x49b004f00db402d8 0x126c013c036d00b6 0x20f000f00ffc03fc 0x483c003c03ff00ff

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x20e000000be00003 0x4838000002f80000

def z465 : W := mkw 0x000000555105070e 0x00000015544141c3 0x601001fff71c031d 0xd804007ffdc700c7

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z467 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xe001010f071f1f1d 0xb8004043c1c7c7c7

def z468 : W := mkw 0x0046820880000000 0x0011a08220000000 0x800ec00cc0000000 0x2003b00330000000

def z469 : W := mkw 0x2cffe6ccc3636360 0x0b3ff9b330d8d8d8 0xfffffecccbe3e3e3 0xffffffb332f8f8f8

def z470 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x40e0ceccc3e003e0 0x503833b330f800f8

def z471 : W := mkw 0xcffffffaaffedad8 0x73fffffeabffb6b6 0xffffffffffffffff 0xffffffffffffffff

def z472 : W := mkw 0x00005050030e0a08 0x0000141400c38282 0xe011f1f0071f1f1d 0xf8047c7c01c7c7c7

def z473 : W := mkw 0x2effefeee3636360 0x4bbffbfbb8d8d8d8 0xffeececccbe3e3e3 0x7ffbb3b332f8f8f8

def z474 : W := mkw 0x0cdde00002424000 0x0337780000909000 0xbffff0000be3e003 0xeffffc0002f8f800

def z475 : W := mkw 0x00005011120e0c0e 0x0000140444838303 0xa011f133371f1c1d 0xe8047c4ccdc7c707

def z476 : W := mkw 0x8d9920000c909000 0x2366480003242400 0x1f00000000000000 0x07c0000000000000

def z477 : W := mkw 0x0066c6ccc3030300 0x0019b1b330c0c0c0 0xe0eececcc3030303 0x783bb3b330c0c0c0

def z478 : W := mkw 0x0ddda0000c900000 0x0377680003240000 0xbffff0000ffc0003 0xeffffc0003ff0000

def z479 : W := mkw 0x1effafafa001b524 0x47bfebebe8006d49 0xdffffffff003fc03 0xf7fffffffc00ff00

def z480 : W := mkw 0x0044800000404000 0x0011200000101000 0x00ee000008e0e002 0x003b800002383800

def z481 : W := mkw 0x8d9970555f9f9f0e 0x23665c1557e7e7c3 0xff11f1fff71f1f1d 0xffc47c7ffdc7c7c7

def z482 : W := mkw 0x030009050c010594 0x00c0024143004165 0xff010f0f0c031fff 0xbfc043c3c300c7ff

def z483 : W := mkw 0x0e997977730f0f0e 0x43a65e5ddcc3c3c3 0xff11f1fff71f1f1d 0xffc47c7ffdc7c7c7

def z484 : W := mkw 0x32220fcfc12127f4 0x0c8883f3f04849fd 0x40000fcfc00003fc 0x100003f3f00000ff

def z485 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xe000c0ccc71f1f1d 0x7800303331c7c7c7

def z486 : W := mkw 0x1fdfab0f0c01b5b4 0x07f7eac3c3006d6d 0xffffff0f0c03ffff 0xffffffc3c300ffff

def z487 : W := mkw 0x00005000020a0800 0x0000140000828200 0x20000000071f1c00 0x0800000001c7c700

def z488 : W := mkw 0x0044800000000000 0x0011200000000000 0x80eec00000000003 0x603bb00000000000

def z489 : W := mkw 0x4bb20ffc0db523f8 0x12ec83ff036d48fe 0xfffe0ffc0fffe3ff 0xffff83ff03fff8ff

def z490 : W := mkw 0x8dfdf4a0aedad800 0x637f7d282bb6b600 0xbffff0f0fffffc03 0xeffffc3c3fffff00

def z491 : W := mkw 0x43200df00db402d8 0x10c8037c036d00b6 0x60000ff00ffc03fc 0x180003fc03ff00ff

def z492 : W := mkw 0x88d4f05553df4f0e 0x22353c1554f7d3c3 0xe0f1f1fff7ff1f1d 0xf83c7c7ffdffc7c7

def z493 : W := mkw 0x4bb00df50db507dc 0x12ec037d436d41f7 0xfff10fff0fff1fff 0xfffc43ffc3ffc7ff

def z494 : W := mkw 0x0000100110080c06 0x0000040044020301 0x0001300330001c00 0x00004c00cc000700

def z495 : W := mkw 0x844df000024ad800 0x21137c000092b600 0xa0eff0000be3fc03 0x683bfc0002f8ff00

def z496 : W := mkw 0x2000404443636360 0x0800101110d8d8d8 0xe000c0cccbe3e3e1 0x7800303332f8f8f8

def z497 : W := mkw 0x9fddf9030edadc94 0x27f77e40c3b6b725 0xbffff1030ffffc1f 0xeffffc40c3ffff07

def z498 : W := mkw 0x4b9009300c940098 0x12e4024c03250026 0x7f100f300c1c03ff 0x9fc403cc030700ff

def z499 : W := mkw 0x12025b5f530f2fbe 0x048096d7d4c3cbef 0xe011fffff71f1ffd 0xf8047ffffdc7c7ff

def z500 : W := mkw 0x00005000520a0802 0x0000140014828200 0x0000f000f0000000 0x00003c003c000000

def z501 : W := mkw 0x0066c68882424000 0x0019b1a220909000 0xe0eececccbe3e003 0x783bb3b332f8f800

def z502 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x1ff1f00007fc1c00 0xc7fc7c0001ff0700

def z503 : W := mkw 0x00005054530f0b0a 0x0000141514c3c2c2 0xe010f0fcf31f0301 0x78043c3f3cc7c0c0

def z504 : W := mkw 0x2064848080604040 0x0819212020181010 0x00e0000000e00000 0x0038000000380000

def z505 : W := mkw 0x170b5b0f5e0bbdb6 0x05c2d6c3d782ef6d 0xff0fff0ffc03ffff 0xbfc3ffc3ff00ffff

def z506 : W := mkw 0x8cddf00002da4800 0x23377c0000b69200 0x9ffff00003fc0003 0xe7fffc0000ff0000

def z507 : W := mkw 0x48b054f553bf0f4e 0x122c153d54efc3d3 0xe0f1f1fff7ff1f1d 0xf83c7c7ffdffc7c7

def z508 : W := mkw 0x9fdffb0a0edaf8b0 0x27f7fec283b6be2c 0xbffffe000ffffce3 0xefffff8003ffff38

def z509 : W := mkw 0x42200df0012402d8 0x1088037c004900b6 0x60100ff0071c03fd 0xd80403fc01c700ff

def z510 : W := mkw 0x572b0fff0d25b7fc 0x15cac3ffc3496dff 0xff0f0fff0c03ffff 0xbfc3c3ffc300ffff

def z511 : W := mkw 0x8ddff20aaedad800 0x6377fc82abb6b600 0xbffff00ffffffc03 0xeffffc03ffffff00

def z512 : W := mkw 0x010000000c900000 0x0040000003240000 0x200000000ffc0000 0x0800000003ff0000

def z513 : W := mkw 0x08f4a4a0a0000000 0x423d292828000000 0xc0f1f1fff0000001 0xf03c7c7ffc000000

def z514 : W := mkw 0x2066c68882626060 0x0819b1a220989818 0xa0eece000be3e0e3 0x683bb38002f8f838

def z515 : W := mkw 0x172b0fafac01b5b4 0x45cac3ebeb006d6d 0xff0f0ffffc03ffff 0xbfc3c3ffff00ffff

def z516 : W := mkw 0x68f6c6fcc3f76368 0x1a3db1bf30fdd8da 0xe0fecefccbffe3e3 0x783fb3bf32fff8f8

def z517 : W := mkw 0x150b020f0c01b524 0x0542c083c3006d49 0xbf0f000f0c03fc03 0xafc3c003c300ff00

def z518 : W := mkw 0x6bf6cfeccff363f0 0x1afdb3fb33fcd8fc 0xffeececccbe3e3e3 0x7ffbb3b332f8f8f8

def z519 : W := mkw 0x2002424c43636360 0x0800909310d8d8d8 0xe00e0e0c0be3e3e3 0x3803838302f8f8f8

def z520 : W := mkw 0x5f9b0b3f0c95b5bc 0x17e6c2cfc3256d6f 0xff1f0f3f0c1fffff 0xbfc7c3cfc307ffff

def z521 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x5fe00ff008e003fe 0x17f803fc023800ff

def z522 : W := mkw 0x00001015100d0d0e 0x0000040544034343 0xe011313f341f1f1d 0xb8044c4fcd07c7c7

def z523 : W := mkw 0x110050555f0fbfbe 0x0440141557c3efef 0x200000000f1ffffc 0x0800000003c7ffff

def z524 : W := mkw 0x0000404443030300 0x0000101110c0c0c0 0xe011f1fff3030301 0xf8047c7ffcc0c0c0

def z525 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x601001f0071f1f1d 0xd804007c01c7c7c7

def z526 : W := mkw 0xdfffffff0ffffffc 0x37ffffffc3ffffff 0xffffffff0fffffff 0xffffffffc3ffffff

def z527 : W := mkw 0x040b020a00000000 0x0102c08280000000 0x800f000f00000000 0x2003c003c0000000

def z528 : W := mkw 0x4b9059755f9f0f9e 0x12e4165d57e7c3e7 0xff11f1fff71f1f1d 0xffc47c7ffdc7c7c7

def z529 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x8011f0fff31f1c00 0x60047c3ffcc7c700

def z530 : W := mkw 0x170909070c01b5b4 0x05c24241c3006d6d 0x3f0101030c03fffc 0x8fc04040c300ffff

def z531 : W := mkw 0x412004d00db402d8 0x10480134036d00b6 0x60e00ec00ffc03ff 0x583803b003ff00ff

def z532 : W := mkw 0x8fddf9000edad890 0x23f77e4003b6b624 0xffffff000fffffff 0xffffffc003ffffff

def z533 : W := mkw 0x0002020800000000 0x0000808200000000 0xc00e0e0c00000003 0x3003838300000000

def z534 : W := mkw 0x4bb00db00cb400d8 0x12ec036c032d0036 0x1ff00f300cfc00fe 0x87fc03cc033f003f

def z535 : W := mkw 0x2002020cc0012120 0x0800808330004848 0x0000000cc0000000 0x0000000330000000

def z536 : W := mkw 0x002044c443230340 0x0008113110c8c0d0 0xe0e0cecccbe303e3 0x783833b332f8c0f8

def z537 : W := mkw 0x4ab00df001b40248 0x12ac037c006d0092 0x5ff00ff003fc0003 0xd7fc03fc00ff0000

def z538 : W := mkw 0x810050555fdfdf0e 0x2040141557f7f7c3 0xe011f1ffffffff1d 0xf8047c7fffffffc7

def z539 : W := mkw 0x88d4a00000d04000 0x2235280000341000 0x00e0000000e00000 0x0038000000380000

def z540 : W := mkw 0x2effafeee1212360 0x4bbfebfbb84848d8 0xdffffffff00003e3 0xf7fffffffc0000f8

def z541 : W := mkw 0x370b4b4f4f63f7f4 0x0dc2d2d3d3d8fdfd 0xff0f0f0f0fe3ffff 0xbfc3c3c3c3f8ffff

def z542 : W := mkw 0x09d4c0000ed24000 0x0275300003b49000 0xbffec0000fffe003 0xefffb00003fff800

def z543 : W := mkw 0x4fb92df22db402d8 0x53ee4b7c8b6d00b6 0x7ff13ff33ffc03ff 0xdffc4ffccfff00ff

def z544 : W := mkw 0x00005015520f0d0e 0x000014055483c343 0x8011f13ff41f1c1c 0xa0047c4ffd07c707

def z545 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x9f0f010f0403fc1c 0xa7c3c043c100ff07

def z546 : W := mkw 0x00001011100c0c0e 0x0000040444030303 0x00000000041c1c1c 0x0000000001070707

def z547 : W := mkw 0x2046c24cc3436320 0x0811b09330d0d8c8 0xe00ec0ccc303e301 0x7803b03330c0f8c0

def z548 : W := mkw 0x8fffbfaaac989800 0x63ffefeaab262600 0xdffffffff41c1c03 0xf7fffffffd070700

def z549 : W := mkw 0x170909020c009090 0x05c2424083002424 0x1f00000000000000 0x07c0000000000000

def z550 : W := mkw 0x0066d6ddd30f0f0e 0x0019b5b774c3c3c3 0xe0fffffff71f1f1f 0xf83ffffffdc7c7c7

def z551 : W := mkw 0x570b0b5f0db5b7fc 0x15c2c2d7c36d6dff 0xff0f0f0f0fffffff 0xbfc3c3c3c3ffffff

def z552 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xa011f000071f1f1d 0xe8047c0001c7c7c7

def z553 : W := mkw 0x344fc20fc243f524 0x0d13f083f090fd49 0x800fc00fc003fc00 0x2003f003f000ff00

def z554 : W := mkw 0x0af6afaaa0000000 0x42bdabeaa8000000 0x40f0fffff0000000 0x503c3ffffc000000

def z555 : W := mkw 0x13020b0f0c01b5b4 0x04c082c3c3006d6d 0x60000f0f0c03fffc 0x180003c3c300ffff

def z556 : W := mkw 0x03200dc00d2002d0 0x00c80370034800b4 0x7fe00fc00fe003ff 0xdff803f003f800ff

def z557 : W := mkw 0x1fffafaaac00b0b0 0x47ffebeaab002c2c 0xdffffffff800e0e3 0xf7fffffffe003838

def z558 : W := mkw 0x050900050c019504 0x0142400143006541 0xff0f010f0c03ff1f 0xbfc3c043c300ffc7

def z559 : W := mkw 0x0000000500010504 0x0000000140004141 0xe011f1fff4031f1d 0xf8047c7ffd00c7c7

def z560 : W := mkw 0x9ddff20f0edbfd24 0x2777fc83c3b6ff49 0xbffff00f0ffffc03 0xeffffc03c3ffff00

def z561 : W := mkw 0x00001010100c080a 0x0000040404030202 0x00103030301c0000 0x00040c0c0c070000

def z562 : W := mkw 0x4bb01df11dbc0ede 0x12ec077c476f03b7 0x7ff13ff33ffc1fff 0xdffc4ffccfff07ff

def z563 : W := mkw 0xcbf4fdf00ffe4ad8 0x32fd3f7c03ff92b6 0x7ff0fff00ffc03ff 0xdffc3ffc03ff00ff

def z564 : W := mkw 0x13020b0f0c0125b4 0x04c082c3c300496d 0x7f000f0f0c0003ff 0x9fc003c3c30000ff

def z565 : W := mkw 0x0effbfbbb00c0c0e 0x43bfefeeec030303 0xdffffffff41c1c1f 0xf7fffffffd070707

def z566 : W := mkw 0x5bb00df50db5b7fc 0x16ec037d436d6dff 0x7ff00ff00fffffff 0xdffc03fc03ffffff

def z567 : W := mkw 0xcffdfda00efad8d0 0x33ff7f6803beb634 0xbffffe000ffffce3 0xefffff8003ffff38

def z568 : W := mkw 0x88d4f05053de4a0a 0x22353c1414f79282 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z569 : W := mkw 0x170b0b0a0c00b0b0 0x05c2c2c283002c2c 0xbf0f0e000c03fce3 0xafc3c3800300ff38

def z570 : W := mkw 0x12020b0a000020b0 0x048082c28000082c 0x00000e00000000e0 0x0000038000000038

def z571 : W := mkw 0x8dddb0000cd8d800 0x23776c0003363600 0x1fff30000cfcfc02 0x87ffcc00033f3f00

def z572 : W := mkw 0x000000550105070c 0x00000015404141c3 0xe01101ff071f1f1d 0xf804407fc1c7c7c7

def z573 : W := mkw 0x4200093000040098 0x1080024c00010026 0x000001300000001c 0x0000004c00000007

def z574 : W := mkw 0x050b020c0c01b120 0x0142c08303006c48 0xff0f0e0c0c03ffe3 0xbfc3c3830300fff8

def z575 : W := mkw 0x0bb00da00c000090 0x02ec036803000024 0x7ff00ff00c0003ff 0xdffc03fc030000ff

def z576 : W := mkw 0x88f4f4a0a2da4800 0x623d3d2828b69200 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z577 : W := mkw 0x8dddf0111ededc0e 0x23777c0447b7b703 0xbffff1333ffffc1f 0xeffffc4ccfffff07

def z578 : W := mkw 0x099000500d940208 0x0264001403650082 0x7ff001f00ffc031f 0xdffc007c03ff00c7

def z579 : W := mkw 0xa44ff20cc24bf920 0x2913fc833092fe48 0x800ff00cc003fc00 0x2003fc033000ff00

def z580 : W := mkw 0x410000500db402d8 0x10400014036d00b6 0x601001f00ffc03fd 0xd804007c03ff00ff

def z581 : W := mkw 0x0044c00002424000 0x0011300000909000 0x800ec0000003e000 0x2003b0000000f800

def z582 : W := mkw 0x202246ccc3232360 0x080891b330c8c8d8 0xe000ceccc30303e1 0x780033b330c0c0f8

def z583 : W := mkw 0x8cddf00002dad800 0x23377c0000b6b600 0x80fff00003fffc00 0x603ffc0000ffff00

def z584 : W := mkw 0x8dddf0050edbdd04 0x23777c0143b6f741 0xfffff10f0fffff1f 0xfffffc43c3ffffc7

def z585 : W := mkw 0x08f4a4a0a0000000 0x423d292828000000 0x00e0000000000000 0x0038000000000000

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0x20100000071c0001 0xc804000001c70000

def z587 : W := mkw 0x0044c00002424000 0x0011300000909000 0x00e0c00003e00000 0x4038300000f80000

def z588 : W := mkw 0x4effaffaa12402d8 0x53bfebfea84900b6 0xdffffffff00003ff 0xf7fffffffc0000ff

def z589 : W := mkw 0x110000010c009494 0x0440000043002525 0x0000000004001c1c 0x0000000001000707

def z590 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x5f100ff0041c03fc 0x97c403fc010700ff

def z591 : W := mkw 0x810000000cd0d000 0x2040000003343400 0x0000000008e0e000 0x0000000002383800

def z592 : W := mkw 0x8ddff20c0edbf920 0x2377fc8303b6fe48 0xfffffe0c0fffffe3 0xffffff8303fffff8

def z593 : W := mkw 0x1fffafabac009494 0x47ffebeaeb002525 0xdffffffff4001c1f 0xf7fffffffd000707

def z594 : W := mkw 0x030009000c000090 0x00c0024003000024 0x1f000e00080000e2 0x07c0038002000038

def z595 : W := mkw 0x1fbb0faf0c01b5b4 0x07eec3ebc3006d6d 0xffff0fff0c03ffff 0xffffc3ffc300ffff

def z596 : W := mkw 0x4bf4cdf00ff642d8 0x12fd337c03fd90b6 0xfffecff00fffe3ff 0xffffb3fc03fff8ff

def z597 : W := mkw 0x140b020a0000b020 0x0502c08280002c08 0x000e00000000e000 0x0003800000003800

def z598 : W := mkw 0x9fffffafaedbfdb4 0x67ffffebebb6ff6d 0xffffffffffffffff 0xffffffffffffffff

def z599 : W := mkw 0x1200090300000494 0x04800240c0000125 0x000001030000001c 0x00000040c0000007

def z600 : W := mkw 0x4bb05df05fbe0ada 0x12ec177c17ef82b6 0x7ff0fff0fffc03ff 0xdffc3ffc3fff00ff

def z601 : W := mkw 0x0000004001200240 0x0000001000480090 0x200000000be003e0 0x0800000002f800f8

def z602 : W := mkw 0x044ff20ff20b0d06 0x4113fc83fc82c341 0x800ff00ff0031c00 0x2003fc03fc00c700

def z603 : W := mkw 0x0000004441010300 0x00000011104040c0 0x400000ccc0000300 0x10000033300000c0

def z604 : W := mkw 0x2064d4d0d36e4a4a 0x0819353434db9292 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z605 : W := mkw 0xa8f6f6ccc3fb6b60 0x2a3dbdb330fedad8 0xe0fefecccbffe3e3 0x783fbfb332fff8f8

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010f0f0f0000000 0x40043c3c3c000000

def z607 : W := mkw 0x12020b0f000125b4 0x048082c3c000496d 0xe0010f0f04031ffd 0xb80043c3c100c7ff

def z608 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xdfef0f0f00000003 0xb7fbc3c3c0000000

def z609 : W := mkw 0x00005000020a0800 0x0000140000828200 0x8001f00000031c00 0x20007c000000c700

def z610 : W := mkw 0x4000005001b40248 0x10000014006d0092 0x0000000003fc0000 0x0000000000ff0000

def z611 : W := mkw 0x2af6cfecc3636360 0x0abdb3fb30d8d8d8 0xfffecffccbe3e3e3 0xffffb3ff32f8f8f8

def z612 : W := mkw 0x0af4ada0a0000000 0x42bd2b6828000000 0x5ff0fff0f0000003 0xd7fc3ffc3c000000

def z613 : W := mkw 0x4bb00da00cb000d0 0x12ec0368032c0034 0x7fe00f000ce003ff 0x9ff803c0033800ff

def z614 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x5ffe0ff000000003 0xd7ff83fc00000000

def z615 : W := mkw 0x844df000024ad800 0x21137c000092b600 0xa01ff000071ffc01 0xe807fc0001c7ff00

def z616 : W := mkw 0x6266cffcc36763f8 0x1899b3ff30d9d8fe 0xe0eecffccbe3e3ff 0x783bb3ff32f8f8ff

def z617 : W := mkw 0x4f9929322c940098 0x53e64a4c8b250026 0x1f113133341c001c 0x87c44c4ccd070007

def z618 : W := mkw 0x1409000300009404 0x05024000c0002501 0x0001000300001c00 0x00004000c0000700

def z619 : W := mkw 0x002054d5532f0f4e 0x0008153554cbc3d3 0xe0f1ffffffff1fff 0xf83c7fffffffc7ff

def z620 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x5f010f0f04001ffc 0x97c043c3c10007ff

def z621 : W := mkw 0x176f8f8f8c01b5b4 0x05dbe3e3e3006d6d 0xffefcfcfcc03ffff 0xfffbf3f3f300ffff

def z622 : W := mkw 0x2022068880202060 0x080881a220080818 0x00000e00000000e0 0x0000038000000038

def z623 : W := mkw 0xc10050500ffedad8 0x3040141403ffb6b6 0x200000000ffffffc 0x0800000003ffffff

def z624 : W := mkw 0x0ab20faaa0000000 0x42ac83eaa8000000 0x5ff00ffff0000003 0xd7fc03fffc000000

def z625 : W := mkw 0x060b0b0a00000000 0x0182c2c280000000 0x1f0e0e0000000002 0x07c3838000000000

def z626 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x1fff3f3330000002 0x87ffcfcccc000000

def z627 : W := mkw 0x0890000000900000 0x0224000000240000 0x00f0000003fc0000 0x403c000000ff0000

def z628 : W := mkw 0x0ab05df5530f0f0e 0x02ac177d54c3c3c3 0xfff1fffff71f1f1f 0xfffc7ffffdc7c7c7

def z629 : W := mkw 0x6fffeffeeff763f8 0x5bfffbffbbfdd8fe 0xffffffffffffe3ff 0xfffffffffffff8ff

def z630 : W := mkw 0x0ddda0000c009000 0x0377680003002400 0xbffff0000c03fc03 0xeffffc000300ff00

def z631 : W := mkw 0xcfddf9300eded898 0x33f77e4c03b7b626 0xbffff1300ffffc1f 0xeffffc4c03ffff07

def z632 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xc001f1fff0031f1c 0x30007c7ffc00c7c7

def z633 : W := mkw 0x140b020f0001b524 0x0502c083c0006d49 0xe00f010f0403ff1d 0xb803c043c100ffc7

def z634 : W := mkw 0x4bf4adf0adb402d8 0x52fd2b7c2b6d00b6 0x7ff0fff0fffc03ff 0xdffc3ffc3fff00ff

def z635 : W := mkw 0x0ab00de001200240 0x02ac037800480090 0x7ff00ff00be003e3 0xdffc03fc02f800f8

def z636 : W := mkw 0x8effffaaa2da4800 0x63bfffeaa8b69200 0xdffffffff3fc0003 0xf7fffffffcff0000

def z637 : W := mkw 0x0000005001040208 0x0000001400410082 0x20000000071c031c 0x0800000001c700c7

def z638 : W := mkw 0x0066868c80012120 0x0019a1a320004848 0xe0eececcc803e3e3 0x783bb3b33200f8f8

def z639 : W := mkw 0x4bb05df55fbf0fde 0x12ec177d57efc3f7 0x7ff00ff00fff1fff 0xdffc03fc03ffc7ff

def z640 : W := mkw 0x110000000c00b0b0 0x0440000003002c2c 0x000000000800e0e0 0x0000000002003838

def z641 : W := mkw 0x8ddde0000ed2d000 0x2377780003b4b400 0xbfeec0000be3e003 0x6ffbb00002f8f800

def z642 : W := mkw 0xadfdf4c0cffada40 0x2b7f7d3033feb690 0xbffff0c0cffffc03 0xeffffc3033ffff00

def z643 : W := mkw 0x0000000500010504 0x0000000140004141 0x2000000004031f1c 0x080000000100c7c7

def z644 : W := mkw 0x002004d001240248 0x0008013400490092 0x60f00ff00ffc03ff 0xd83c03fc03ff00ff

def z645 : W := mkw 0x0ebb2faaa0000000 0x43aecbeaa8000000 0x5f113ffff0000000 0x97c44ffffc000000

def z646 : W := mkw 0x22220feee1212360 0x488883fbb84848d8 0x40000ffff00003e0 0x100003fffc0000f8

def z647 : W := mkw 0x002004c001200240 0x0008013000480090 0x40000ec0000003e0 0x100003b0000000f8

def z648 : W := mkw 0x0cddf055530f0f0e 0x03377c1554c3c3c3 0xfffff1fff71f1f1f 0xfffffc7ffdc7c7c7

def z649 : W := mkw 0x62220ffcc12523f8 0x188883ff304948fe 0x40000ffcc00003fc 0x100003ff300000ff

def z650 : W := mkw 0x0ab00df001040208 0x02ac037c00410082 0x7ff00ff0071c031f 0xdffc03fc01c700c7

def z651 : W := mkw 0x0cddf000020a0800 0x03377c0000828200 0xbffff000071f1c03 0xeffffc0001c7c700

def z652 : W := mkw 0x0000404543030704 0x0000101150c0c1c1 0xe001c1cfc7031f1d 0xf8007073f1c0c7c7

def z653 : W := mkw 0x00005050530e0a0a 0x0000141414c38282 0x00000000031c0000 0x0000000000c70000

def z654 : W := mkw 0x0000400002424000 0x0000100000909000 0x200000000be3e000 0x0800000002f8f800

def z655 : W := mkw 0x066fafaaa0000000 0x419bebeaa8000000 0xc00ffffff0000000 0x3003fffffc000000

def z656 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x9f0f0e0f0803fce2 0x27c3c383c200ff38

def z657 : W := mkw 0x010000000c009000 0x0040000003002400 0x200000000c03fc00 0x080000000300ff00

def z658 : W := mkw 0x2064c4c0c3624240 0x0819313030d89090 0xa0eec0c0cbe3e003 0x683bb03032f8f800

def z659 : W := mkw 0x00005005520b0d06 0x000014015482c341 0x0000000000031c00 0x000000000000c700

def z660 : W := mkw 0x170b0b0b0c00b4b4 0x05c2c2c2c3002d2d 0x1f0f0f030c00fcfe 0x87c3c3c0c3003f3f

def z661 : W := mkw 0xafffffeeeffbfb60 0x6bfffffbbbfefed8 0xffffffffffffffe3 0xfffffffffffffff8

def z662 : W := mkw 0x0000000000000000 0x0000000000000000 0x400001fff0000000 0x1000007ffc000000

def z663 : W := mkw 0x202206ddd125276e 0x080881b7744949db 0x40000ffff00003fc 0x100003fffc0000ff

def z664 : W := mkw 0x410000100c940098 0x1040000403250026 0x00000000041c001c 0x0000000001070007

def z665 : W := mkw 0x0eb92da220000000 0x43ae4b6888000000 0x5ff13ff330000003 0xd7fc4ffccc000000

def z666 : W := mkw 0x0000004001000200 0x0000001000400080 0x600000c003000301 0x5800003000c000c0

def z667 : W := mkw 0x80005000024ad800 0x200014000092b600 0x000000000003fc00 0x000000000000ff00

def z668 : W := mkw 0x03020b0c0c0121b0 0x00c082c30300486c 0xff0e0f0c0c03e3ff 0xbfc383c30300f8ff

def z669 : W := mkw 0x5fbb0ffa0db4b2f8 0x17eec3fe836d2cbe 0x7ffe0ff00ffce3ff 0xdfff83fc03ff38ff

def z670 : W := mkw 0x8dddf0444fdbdb00 0x23777c1113f6f6c0 0xfffff0cccfffff03 0xfffffc3333ffffc0

def z671 : W := mkw 0x110000050c01b5b4 0x0440000143006d6d 0xe001010f0c03fffd 0xb8004043c300ffff

def z672 : W := mkw 0x050900000c009000 0x0142400003002400 0x1f0e00000800e002 0x07c3800002003800

def z673 : W := mkw 0x02220faaa0000000 0x408883eaa8000000 0xc011fffff0000001 0xf0047ffffc000000

def z674 : W := mkw 0x100000050001b524 0x0400000140006d49 0x000000000003fc00 0x000000000000ff00

def z675 : W := mkw 0x4ab00df001b402d8 0x12ac037c006d00b6 0x40f00ff003fc03fc 0x503c03fc00ff00ff

def z676 : W := mkw 0x0cfda4a0a0000000 0x433f692828000000 0x9ffff0f0f0000003 0xe7fffc3c3c000000

def z677 : W := mkw 0x5fb90df30db496dc 0x17ee437cc36d25b7 0x7ff10ff30ffc1fff 0xdffc43fcc3ff07ff

def z678 : W := mkw 0x4bb04df44fb703d8 0x12ec137d13edc0f6 0xfff0cffccfff03ff 0xfffc33ff33ffc0ff

def z679 : W := mkw 0x42200da0002000d0 0x1088036800080034 0x00000e00000000e0 0x0000038000000038

def z680 : W := mkw 0x170b0b0b0c009494 0x05c2c2c2c3002525 0xdf0f0f0f04001c1f 0xb7c3c3c3c1000707

def z681 : W := mkw 0x070b0b0a0c009000 0x01c2c2c283002400 0xff0f0f0f0c03fc03 0xbfc3c3c3c300ff00

def z682 : W := mkw 0x4bb00da00cb000d0 0x12ec0368032c0034 0x5ff00ff008e000e3 0xd7fc03fc02380038

def z683 : W := mkw 0x8ffdfda00edad800 0x23ff7f6803b6b600 0xfffffff00ffffc03 0xfffffffc03ffff00

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x600001000400031d 0x98000040010000c7

def z685 : W := mkw 0x150900050c01b5b4 0x0542400143006d6d 0xbf0f00000c03ffff 0xafc3c0000300ffff

def z686 : W := mkw 0x050900000c009000 0x0142400003002400 0x1f01000004001c00 0x87c0400001000700

def z687 : W := mkw 0x6bb20ffccdb523f8 0x1aec83ff336d48fe 0x7ff00ffccffc03ff 0xdffc03ff33ff00ff

def z688 : W := mkw 0x10000005000125b4 0x040000014000496d 0x00000000000003fc 0x00000000000000ff

def z689 : W := mkw 0x48f4a4f0a1b40248 0x523d293c286d0092 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z690 : W := mkw 0x6bf68fa88cf060f0 0x1afda3ea233c183c 0x1fee0e0008e0e0e2 0x07fb838002383838

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001f00ff0000000 0x20007c03fc000000

def z692 : W := mkw 0x044fa20aa0000000 0x4113e882a8000000 0xc01ff1fff0000001 0xf007fc7ffc000000

def z693 : W := mkw 0x8fffafaaacd0d000 0x63ffebeaab343400 0x1fee0e0008e0e002 0x07fb838002383800

def z694 : W := mkw 0x0002525d530f2f2e 0x0000949754c3cbcb 0xe01fffffff1fffff 0xf807ffffffc7ffff

def z695 : W := mkw 0x140b520f520bbd26 0x0502d483d482ef49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z696 : W := mkw 0x0000404043020200 0x0000101010c08080 0x0000c0c0c3000000 0x4000303030c00000

def z697 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xdfeececcc0000003 0x77fbb3b330000000

def z698 : W := mkw 0x402004f001240248 0x1008013c00490092 0x000000f000000000 0x0000003c00000000

def z699 : W := mkw 0x002004a0a0000000 0x4008012828000000 0x000000f0f0000000 0x0000003c3c000000

def z700 : W := mkw 0x29f6c6cccff36360 0x0a7db1b333fcd8d8 0xfffececccfffe3e3 0xffffb3b333fff8f8

def z701 : W := mkw 0x8ddda0000cd0d000 0x2377680003343400 0x9ffff00008e0e003 0xe7fffc0002383800

def z702 : W := mkw 0x5fbb5fff5fbfbffe 0x17eed7ffd7efefff 0xffffffffffffffff 0xffffffffffffffff

def z703 : W := mkw 0x170919131c0c9c9e 0x05c24644c7032727 0x1f113133341c1c1c 0x87c44c4ccd070707

def z704 : W := mkw 0x854df0000edad800 0x21537c0003b6b600 0xa00ff0000ffffc00 0x2803fc0003ffff00

def z705 : W := mkw 0x899050000edad800 0x2264140003b6b600 0x3ff000000ffffc03 0xcffc000003ffff00

def z706 : W := mkw 0x0fffafaaac009000 0x43ffebeaab002400 0xfffffffffc03fc03 0xffffffffff00ff00

def z707 : W := mkw 0x5f9909770d95979c 0x17e6425dc36565e7 0xff1101ff071f1f1d 0xffc4407fc1c7c7c7

def z708 : W := mkw 0x0cddf000024a4800 0x03377c0000929200 0xbffff0000ffffc03 0xeffffc0003ffff00

def z709 : W := mkw 0x0064d4d0036e4a48 0x0019353400db9292 0xe0fffff00fffffff 0xf83ffffc03ffffff

def z710 : W := mkw 0x5cbb06ff01b5b76c 0x172ec1bfc06d6ddb 0x80ff00ff03fffc00 0x603fc03fc0ffff00

def z711 : W := mkw 0x0cfda4a0a0000000 0x433f692828000000 0xdffff1fff0000003 0xf7fffc7ffc000000

def z712 : W := mkw 0x2066c6ddc367676c 0x0819b1b770d9d9db 0xe0ffcfffcfffffff 0xf83ff3fff3ffffff

def z713 : W := mkw 0x1f9909030c909494 0x07e64240c3242525 0x1f110103041c1c1c 0x87c44040c1070707

def z714 : W := mkw 0x00005055532f0f4e 0x0000141554cbc3d3 0xe011f1ffffff1ffd 0xf8047c7fffffc7ff

def z715 : W := mkw 0x064fab0aa0000000 0x4193eac2a8000000 0xdf1ffffff0000003 0xf7c7fffffc000000

def z716 : W := mkw 0x2066d6ccc36b6b60 0x0819b5b330dadad8 0xe0effecccbe3ffe3 0x783bffb332f8fff8

def z717 : W := mkw 0x2066d6d8d36e6a6a 0x0819b5b634db9a9a 0x00fefef0fbfce0e2 0x403fbfbc3eff3838

def z718 : W := mkw 0xcf9979700f9e9a98 0x33e65e5c03e7a6a6 0xff11f1f0071f1f1d 0xffc47c7c01c7c7c7

def z719 : W := mkw 0x0066c6c883624240 0x0019b1b220d89090 0xe0eececccbe3e3e3 0x783bb3b332f8f8f8

def z720 : W := mkw 0x170909050c01b5b4 0x05c2424143006d6d 0xff0f0f000c03ffff 0xbfc3c3c00300ffff

def z721 : W := mkw 0xadbb36cccdb9bb60 0x2b6ecdb3336e6ed8 0x5f113eccc41c1fe0 0x97c44fb3310707f8

def z722 : W := mkw 0xc66dfdf0036edad8 0x319b7f7c00dbb6b6 0xc00ffff00003fffc 0x3003fffc0000ffff

def z723 : W := mkw 0x062b0faaa0000000 0x418ac3eaa8000000 0xdf1ffffff0000003 0xf7c7fffffc000000

def z724 : W := mkw 0x2066d68dd26b6d66 0x0819b5a3749adb59 0x80effe0ff8e3fce2 0x203bff83fe38ff38

def z725 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0xfff0cffccffc03ff 0xfffc33ff33ff00ff

def z726 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0fececccfffe3e3 0xf83fb3b333fff8f8

def z727 : W := mkw 0xcf9929300c949098 0x33e64a4c03252426 0x1f100130041c001c 0x87c4004c01070007

def z728 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x3ff00f300ffc03fe 0x8ffc03cc03ff00ff

def z729 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xa0eece000be3e3e3 0x683bb38002f8f8f8

def z730 : W := mkw 0x202246cc43636360 0x080891b310d8d8d8 0xe0ee0ecc0be3e3e3 0x783b83b302f8f8f8

def z731 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x7fe00f000ffc03ff 0x9ff803c003ff00ff

def z732 : W := mkw 0x2066c6cdc3636764 0x0819b1b370d8d9d9 0xe0eececccfe3ffff 0x783bb3b333f8ffff

def z733 : W := mkw 0x20669699906c6c6e 0x0819a5a6641b1b1b 0x00ff3f333cfcfcfe 0x803fcfcccf3f3f3f

def z734 : W := mkw 0x060b0b0f00012524 0x0182c2c3c0004949 0xff0f0f0f0c03ffff 0xbfc3c3c3c300ffff

def z735 : W := mkw 0x050b020d0c01b524 0x0142c08343006d49 0xff0f0f0f0c03ffff 0xbfc3c3c3c300ffff

def z736 : W := mkw 0x2066d6cdd36b6f66 0x0819b5b374dadbd9 0xe0fffecfffffffe3 0xf83fffb3fffffff8

def z737 : W := mkw 0x0046c20802426020 0x0011b08200909808 0xa0eece000be3e0e3 0x683bb38002f8f838

def z738 : W := mkw 0x09d4d0000eda4800 0x0275340003b69200 0xbffff0000ffffc03 0xeffffc0003ffff00

def z739 : W := mkw 0x83225faaaedad800 0x60c897eaabb6b600 0x60000ffffffffc00 0x180003ffffffff00

def z740 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xbf0f0e0f0c03fffe 0x2fc3c383c300ffff

def z741 : W := mkw 0x170b5b5a5f0ebaba 0x05c2d6d697c3aeae 0x1f1efef0fb1ce0e2 0x47c7bfbc3ec73838

def z742 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0x20ee0e000ffffffe 0x083b838003ffffff

def z743 : W := mkw 0xa44ff20dd24bfd26 0x2913fc837492ff49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z744 : W := mkw 0x376dcdc3cf62d6d4 0x0ddb7370f3d8b5b5 0x1fe1c1c3c7e01c1c 0xc7f87070f1f80707

def z745 : W := mkw 0x2066e6cce3636360 0x4819b9b338d8d8d8 0xe0eefeccfbe3e3e3 0x783bbfb33ef8f8f8

def z746 : W := mkw 0x0af68fa880000000 0x02bda3ea20000000 0xdffffffff0000003 0xf7fffffffc000000

def z747 : W := mkw 0x2066d6dcc36f6b68 0x0819b5b730dbdada 0xe0fffffccfffffff 0xf83fffff33ffffff

def z748 : W := mkw 0x5f9919331c9c9c9e 0x17e6464cc7272727 0x1f113133341c1c1c 0x87c44c4ccd070707

def z749 : W := mkw 0x0edfab0a00000000 0x03b7eac280000000 0xdffffffff0000003 0xf7fffffffc000000

def z750 : W := mkw 0x0edfab2aa0000000 0x43b7eacaa8000000 0xdf1ff1fff0000001 0xf7c7fc7ffc000000

def z751 : W := mkw 0x2066c6cdc3636764 0x0819b1b370d8d9d9 0xe0eecfcfcbe3e3ff 0x783bb3f3f2f8f8ff

def z752 : W := mkw 0x3066c6cfc3636764 0x0c19b1b3f0d8d9d9 0xe0eececfcbe3e3e3 0x783bb3b3f2f8f8f8

def z753 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xbffff1333ffffc03 0xeffffc4ccfffff00

def z754 : W := mkw 0x206686cc81616360 0x0819a1b3205858d8 0xe0ee0ecc0be3e3e3 0x783b83b302f8f8f8

def z755 : W := mkw 0x0cffa68880000000 0x033fe9a220000000 0xdffffffff0000003 0xf7fffffffc000000

def z756 : W := mkw 0x00005005020b0d04 0x000014014082c341 0xe011f1fff71f1f1d 0xf8047c7ffdc7c7c7

def z757 : W := mkw 0x0066c6cc03636360 0x0019b1b300d8d8d8 0xe0eececc0be3e3e3 0x783bb3b302f8f8f8

def z758 : W := mkw 0x0efffffff30f0f0e 0x43bffffffcc3c3c3 0x3fee0e00071f1f1e 0x0ffb838001c7c7c7

def z759 : W := mkw 0x0ab00df001240248 0x02ac037c00490092 0x7ff00ff00ffc03ff 0xdffc03fc03ff00ff

def z760 : W := mkw 0x2046c24c43636360 0x0811b09310d8d8d8 0xe0eece0c0be3e3e3 0x783bb38302f8f8f8

def z761 : W := mkw 0x0609090200000000 0x0182424080000000 0xdf11f1fff0000001 0xf7c47c7ffc000000

def z762 : W := mkw 0x2066c688c2626060 0x0819b1a230989818 0x00eece00c8e0e0e2 0x003bb38032383838

def z763 : W := mkw 0x8ddda0000cd0d000 0x2377680003343400 0xbfff00000ffffc03 0xefffc00003ffff00

def z764 : W := mkw 0x4bb00da00cb000d0 0x12ec0368032c0034 0x7ff00f000ffc03ff 0xdffc03c003ff00ff

def z765 : W := mkw 0x8ddda0555dd5d70e 0x23776815577575c3 0x5fee01fff8e0e31e 0x17fb807ffe3838c7

def z766 : W := mkw 0x20005055534f6f2e 0x0800141554d3dbcb 0xe011f1fff71fff1d 0xf8047c7ffdc7ffc7

def z767 : W := mkw 0x4bb05da55ebb0dd6 0x12ec176957aec375 0x9fe1fe0ff8e31ce2 0x27f87f83fe38c738

def z768 : W := mkw 0x19f4a4a5ac01b5b4 0x467d29296b006d6d 0x20f0f0f0fc03fffc 0x483c3c3c3f00ffff

def z769 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xe011ffffff1f1fff 0xf8047fffffc7c7ff

def z770 : W := mkw 0x9ad6fb0f02db6db4 0x26b5bec3c0b6db6d 0x40f0ff0f03fc03fc 0x503c3fc3c0ff00ff

def z771 : W := mkw 0x6bd6cb3cced761b8 0x1af5b2cf33b5d86e 0x9f1ec13cc41fe01c 0xa7c7b04f3107f807

def z772 : W := mkw 0x0046d20d024b6d24 0x0011b4834092db49 0xe0ffff0f0fffffff 0xf83fffc3c3ffffff

def z773 : W := mkw 0x2066c6ece3636360 0x4819b1bb38d8d8d8 0xe0eecefcfbe3e3e3 0x783bb3bf3ef8f8f8

def z774 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0xfff10ff00fff1fff 0xfffc43fc03ffc7ff

def z775 : W := mkw 0x2066c6cee3636360 0x4819b1b3b8d8d8d8 0xe0eececffbe3e3e3 0x783bb3b3fef8f8f8

def z776 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xbf0f0e000c03ffff 0xafc3c3800300ffff

def z777 : W := mkw 0x0effafaaa0002020 0x43bfebeaa8000808 0xdffffffff800e0e3 0xf7fffffffe003838

def z778 : W := mkw 0x2effafaaa0604040 0x4bbfebeaa8181010 0xdffffffff0e00003 0xf7fffffffc380000

def z779 : W := mkw 0x0cdfa20aa0000000 0x4337e882a8000000 0xdffff1fff0000003 0xf7fffc7ffc000000

def z780 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x3ff00ef00ffc03fe 0x4ffc03bc03ff00ff

def z781 : W := mkw 0x054dd0000e4ad800 0x015374000392b600 0xbffff0000ffffc03 0xeffffc0003ffff00

def z782 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x3ffef0000ffffc02 0x4fffbc0003ffff00

def z783 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0fefefcfbe3e3e3 0x783fbfbf3ef8f8f8

def z784 : W := mkw 0xe8f4f4f0c3fe4a48 0x3a3d3d3c30ff9292 0x00f0f0f0c3fc0000 0x403c3c3c30ff0000

def z785 : W := mkw 0x4bb00df22db402d8 0x52ec037c8b6d00b6 0x7ff00ff33ffc03ff 0xdffc03fccfff00ff

def z786 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x40ee0eccc8e0e0e2 0x103b83b332383838

def z787 : W := mkw 0x2066d6dcd36f6b6a 0x0819b5b734dbdada 0xe0fefffcffffe3ff 0xf83fbfff3ffff8ff

def z788 : W := mkw 0x110050555f0f9f9e 0x0440141557c3e7e7 0x20000000071f1f1c 0x0800000001c7c7c7

def z789 : W := mkw 0x170b0b0f5c01b5b6 0x05c2c2c3d7006d6d 0xff0f0f0ffc03ffff 0xbfc3c3c3ff00ffff

def z790 : W := mkw 0x610050555fff6ffe 0x1840141557ffdbff 0x200000000ffffffc 0x0800000003ffffff

def z791 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0xfff10fff0ffc03ff 0xfffc43ffc3ff00ff

def z792 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff1f0fff0c03ffff 0xffc7c3ffc300ffff

def z793 : W := mkw 0x2e99696663636360 0x4ba65a5998d8d8d8 0x3f1131333be3e3e0 0x8fc44c4ccef8f8f8

def z794 : W := mkw 0x9f9979070e9b9d94 0x27e65e41c3a6e765 0xff11f10f071f1f1d 0xffc47c43c1c7c7c7

def z795 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0xfffe0ff00fffe3ff 0xffff83fc03fff8ff

def z796 : W := mkw 0x0efdada2a0000000 0x43bf6b68a8000000 0xdff1f1fff0000001 0xf7fc7c7ffc000000

def z797 : W := mkw 0x944ff20f524bfd26 0x2513fc83d492ff49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z798 : W := mkw 0xcf9929200c909090 0x33e64a4803242424 0x1f00000000000000 0x07c0000000000000

def z799 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x8011f1fff71f1c1c 0xe0047c7ffdc7c707

def z800 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x5ff1fffff0000000 0xd7fc7ffffc000000

def z801 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xfffffffffbe00003 0xfffffffffef80000

def z802 : W := mkw 0xc10050555fffdfde 0x3040141557fff7f7 0x200000000ffffffc 0x0800000003ffffff

def z803 : W := mkw 0x0bb00dc00db002d0 0x02ec0370036c00b4 0x7ff00fc00ffc03ff 0xdffc03f003ff00ff

def z804 : W := mkw 0x2066c6cdc3636764 0x0819b1b370d8d9d9 0xe0efcecfcbe3ffe3 0x783bf3b3f2f8fff8

def z805 : W := mkw 0x2066c6c883626260 0x0819b1b220d89898 0xe0eecec00be3e3e3 0x783bb3b002f8f8f8

def z806 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0efcfcfcfffffff 0xf83bf3f3f3ffffff

def z807 : W := mkw 0x310050555f6ffffe 0x0c40141557dbffff 0x200000000ffffffc 0x0800000003ffffff

def z808 : W := mkw 0x0efdada000000000 0x03bf6b6800000000 0xdffffffff0000003 0xf7fffffffc000000

def z809 : W := mkw 0x22220ffff125276e 0x488883fffc4949db 0x40000ffff00003fc 0x100003fffc0000ff

def z810 : W := mkw 0x9f9929020c909090 0x27e64a4083242424 0x1f00000000000000 0x07c0000000000000

def z811 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff0f0ffffc03ffff 0xbfc3c3ffff00ffff

def z812 : W := mkw 0x206686d881646268 0x0819a1b62059189a 0x60fe0ff00ffce3ff 0xd83f83fc03ff38ff

def z813 : W := mkw 0x170b0b0f0c91b5b4 0x05c2c2c3c3246d6d 0xff0f0f0f0fffffff 0xbfc3c3c3c3ffffff

def z814 : W := mkw 0xa10050555fffff6e 0x2840141557ffffdb 0x200000000ffffffc 0x0800000003ffffff

def z815 : W := mkw 0x206686ccc1616360 0x0819a1b3305858d8 0xc0eececcc8e0e3e3 0x703bb3b3323838f8

def z816 : W := mkw 0x9f9939232c989c94 0x67e64e48cb262725 0x1f113133341c1c1c 0x87c44c4ccd070707

def z817 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x7f0e0f0f0c03fffe 0x1fc383c3c300ffff

def z818 : W := mkw 0x0effafaaa0200040 0x43bfebeaa8080010 0xdffffffff8e000e3 0xf7fffffffe380038

def z819 : W := mkw 0x0edda92220000000 0x43b76a4888000000 0xdffff1fff0000003 0xf7fffc7ffc000000

def z820 : W := mkw 0x52220fffa12527fc 0x548883ffe84949ff 0x40000ffff00003fc 0x100003fffc0000ff

def z821 : W := mkw 0x03200dd00d2402d8 0x00c80374034900b6 0x7ff00ff00ffc03ff 0xdffc03fc03ff00ff

def z822 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x3ff00e000ffc03ff 0xcffc038003ff00ff

def z823 : W := mkw 0x2066868c80616160 0x0819a1a320185858 0xe0eececcc8e3e3e3 0x783bb3b33238f8f8

def z824 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x7ff00ffffffc03ff 0xdffc03ffffff00ff

def z825 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xdfeffffff0000002 0x37fbfffffc000000

def z826 : W := mkw 0x170b2b0f2c01b5b4 0x45c2cac3cb006d6d 0xff0f3f0f3c03ffff 0xbfc3cfc3cf00ffff

def z827 : W := mkw 0x2066d6dcd36f6b6a 0x0819b5b734dbdada 0xe0fffefcffffffe3 0xf83fffbf3ffffff8

def z828 : W := mkw 0x0b9009500d940298 0x02e40254036500a6 0x7ff00ff00ffc03ff 0xdffc03fc03ff00ff

def z829 : W := mkw 0x0e9b2b2a20000000 0x43a6caca88000000 0xdf1ffffff0000003 0xf7c7fffffc000000

def z830 : W := mkw 0x2066c68cc2636160 0x0819b1a33098d858 0xa0eece0ccbe3e0e3 0x683bb38332f8f838

def z831 : W := mkw 0x2066c6cdd3636766 0x0819b1b374d8d9d9 0xe0eececffbe3e3e3 0x783bb3b3fef8f8f8

def z832 : W := mkw 0x2066c68cc2636160 0x0819b1a33098d858 0xc0eececcc8e3e0e3 0x703bb3b33238f838

def z833 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x9ffffefff0000002 0x67ffffbffc000000

def z834 : W := mkw 0x0022068c00212160 0x000881a300084858 0xe0ee0e0c08e3e3e3 0x383b83830238f8f8

def z835 : W := mkw 0x454fa25aadb402d8 0x5153e896ab6d00b6 0xa00ff00ffffc03fc 0x2803fc03ffff00ff

def z836 : W := mkw 0x2066c68cc2636160 0x0819b1a33098d858 0xe0eece0cc8e3e3e3 0x383bb3833238f8f8

def z837 : W := mkw 0x4effafaaa02000d0 0x53bfebeaa8080034 0xdffffffff00000e3 0xf7fffffffc000038

def z838 : W := mkw 0x0064d4d5536f4f4e 0x0019353554dbd3d3 0xe0ffffffffffffff 0xf83fffffffffffff

def z839 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xfffffffff4031c03 0xfffffffffd00c700

def z840 : W := mkw 0x2066c6dcc3676368 0x0819b1b730d9d8da 0xe0eecffccbe3e3ff 0x783bb3ff32f8f8ff

def z841 : W := mkw 0x2066d6dcd36f6b6a 0x0819b5b734dbdada 0xe0fffffffbffe3e3 0xf83ffffffefff8f8

def z842 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x7f0e0f000c03ffff 0x9fc383c00300ffff

def z843 : W := mkw 0xa8f4f4d0d3fe4a4a 0x2a3d3d3434ff9292 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z844 : W := mkw 0x20005055532f2f6e 0x0800141554cbcbdb 0xe011f1fff71f1ffd 0xf8047c7ffdc7c7ff

def z845 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0effffffbe3ffff 0x783bfffffef8ffff

def z846 : W := mkw 0x010050555f0f0f9e 0x0040141557c3c3e7 0x200000000f1f1ffc 0x0800000003c7c7ff

def z847 : W := mkw 0x68f4d4f0d3fe4a4a 0x1a3d353c34ff9292 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z848 : W := mkw 0x0effafaaa0404000 0x43bfebeaa8101000 0xdffffffff8e0e003 0xf7fffffffe383800

def z849 : W := mkw 0x0044c00002424000 0x0011300000909000 0xe0eece000be3e3e3 0x783bb38002f8f8f8

def z850 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xfffffffff71c0003 0xfffffffffdc70000

def z851 : W := mkw 0x0002020c00012120 0x0000808300004848 0xe0ee0e0c0be3e3e3 0x783b838302f8f8f8

def z852 : W := mkw 0x28f4f4f0f36e4a4a 0x4a3d3d3c3cdb9292 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z853 : W := mkw 0xcf9979755f9f9f9e 0x33e65e5d57e7e7e7 0xff11f1fff71f1f1d 0xffc47c7ffdc7c7c7

def z854 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xfffffe000fffffe3 0xffffff8003fffff8

def z855 : W := mkw 0x2066c6ddd367676e 0x0819b1b774d9d9db 0xe0fecfffffffe3ff 0xf83fb3fffffff8ff

def z856 : W := mkw 0x2066d6ccd36b6b62 0x0819b5b334dadad8 0xe0eefeccfbe3e3e3 0x783bbfb33ef8f8f8

def z857 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0x4011f1fff71c1f1c 0xd0047c7ffdc707c7

def z858 : W := mkw 0x0ebb0faa00000000 0x03aec3ea80000000 0xdffffffff0000003 0xf7fffffffc000000

def z859 : W := mkw 0x0046820800406020 0x0011a08200101808 0x00ee0e0008e0e0e2 0x003b838002383838

def z860 : W := mkw 0x810050555f9f9f0e 0x2040141557e7e7c3 0x20000000071f1f1c 0x0800000001c7c7c7

def z861 : W := mkw 0x2066868880606060 0x0819a1a220181818 0xc0fffffff8e0e0e3 0xf03ffffffe383838

def z862 : W := mkw 0x2effafaaa0406020 0x4bbfebeaa8101808 0xdffffffff000e003 0xf7fffffffc003800

def z863 : W := mkw 0x070b0b0c0c01b1b0 0x01c2c2c303006c6c 0xff0f0f0c0c03ffff 0xbfc3c3c30300ffff

def z864 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x80eececccbe3e0e2 0x603bb3b332f8f838

def z865 : W := mkw 0x8dddf0005edad802 0x23777c0017b6b600 0xbffff000fffffc03 0xeffffc003fffff00

def z866 : W := mkw 0x2066c6cdc3636764 0x0819b1b370d8d9d9 0xe0ffffffffe3ffff 0xf83ffffffff8ffff

def z867 : W := mkw 0x854dd0000edad800 0x2153740003b6b600 0xbfefc0000ffffc03 0xeffbf00003ffff00

def z868 : W := mkw 0x8dddf0022edad800 0x63777c008bb6b600 0xbffff0033ffffc03 0xeffffc00cfffff00

def z869 : W := mkw 0x8f9939000c989890 0x23e64e4003262624 0x1f113100041c1c1c 0x87c44c4001070707

def z870 : W := mkw 0x9f9979575f9f9f9e 0x27e65e55d7e7e7e7 0xff11f1fff71f1f1d 0xffc47c7ffdc7c7c7

def z871 : W := mkw 0x244ff20ff24b6d26 0x4913fc83fc92db49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z872 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xa0eece0ccbe3e3e2 0x283bb38332f8f8f8

def z873 : W := mkw 0x0200090000000000 0x0080024000000000 0xdf11fffff0000003 0xf7c47ffffc000000

def z874 : W := mkw 0x206686ddd165676e 0x0819a1b7745959db 0x40ee0ffff8e0e3fe 0x103b83fffe3838ff

def z875 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff1f3f3f3c03ffff 0xbfc7cfcfcf00ffff

def z876 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xdf0f0f0f0803fffe 0x37c3c3c3c200ffff

def z877 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xc0eececcc8e3e3e2 0x303bb3b33238f8f8

def z878 : W := mkw 0x206686c8c1606260 0x0819a1b230581898 0x00ee0ec0c8e0e0e2 0x003b83b032383838

def z879 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0ee0e0c0be3e3e3 0x383b838302f8f8f8

def z880 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x40eececccbe0e3e2 0x503bb3b332f838f8

def z881 : W := mkw 0x8effafaaa040d000 0x63bfebeaa8103400 0xdffffffff000e003 0xf7fffffffc003800

def z882 : W := mkw 0x0064c48002624040 0x0019312000989010 0xa0eece000be3e0e3 0x683bb38002f8f838

def z883 : W := mkw 0x00005055530f2f2e 0x0000141554c3cbcb 0xe011f1ffff1ffffd 0xf8047c7fffc7ffff

def z884 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x20eecec0cbe3e3e2 0x483bb3b032f8f8f8

def z885 : W := mkw 0x2066d6cdd36b6f66 0x0819b5b374dadbd9 0xe0eececccbe3ffe3 0x783bb3b332f8fff8

def z886 : W := mkw 0xcf9939311c9c9c9e 0x33e64e4c47272727 0x1f113133341c1c1c 0x87c44c4ccd070707

def z887 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x60ee0ec00be3e3e3 0x583b83b002f8f8f8

def z888 : W := mkw 0x070909050c019594 0x01c2424143006565 0xff0f0f0f0c03ffff 0xbfc3c3c3c300ffff

def z889 : W := mkw 0x170b0b0fac01b5b4 0x45c2c2c3eb006d6d 0xff0f0f0ffc03ffff 0xbfc3c3c3ff00ffff

def z890 : W := mkw 0x5f9909230c909494 0x17e64248c3242525 0x1f01010304001c1c 0x87c04040c1000707

def z891 : W := mkw 0x070b0b0a0c009090 0x01c2c2c283002424 0xff0f0f0f0c03ffff 0xbfc3c3c3c300ffff

def z892 : W := mkw 0x002246cc43232360 0x000891b310c8c8d8 0xe0eececccbe3e3e3 0x783bb3b332f8f8f8

def z893 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xe01ff1ffff1fff1f 0xf807fc7fffc7ffc7

def z894 : W := mkw 0x0effafaaa0900000 0x43bfebeaa8240000 0xdffffffff3fc0003 0xf7fffffffcff0000

def z895 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0efcecccfe3ffe3 0xf83bf3b333f8fff8

def z896 : W := mkw 0x20005055536f4f4e 0x0800141554dbd3d3 0xe011f1fff7ff1f1d 0xf8047c7ffdffc7c7

def z897 : W := mkw 0x49b004d00db402d8 0x126c0134036d00b6 0x7ff00ec00ffc03ff 0xdffc03b003ff00ff

def z898 : W := mkw 0x72220fffc12527fc 0x1c8883fff04949ff 0x40000fffc00003fc 0x100003fff00000ff

def z899 : W := mkw 0x9f9939131c9c9c9e 0x27e64e44c7272727 0x1f113133341c1c1c 0x87c44c4ccd070707

def z900 : W := mkw 0x00001015100d0d0e 0x0000040544034343 0xe011f1fff41f1f1d 0xf8047c7ffd07c7c7

def z901 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x80eece0008e0e0e3 0x603bb38002383838

def z902 : W := mkw 0x0a90092000000000 0x02a4024800000000 0xdf11f1fff0000001 0xf7c47c7ffc000000

def z903 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x9ffff0000bfffc02 0x67fffc0002ffff00

def z904 : W := mkw 0x09b004d00db40248 0x026c0134036d0092 0x7ff00ff00ffc03ff 0xdffc03fc03ff00ff

def z905 : W := mkw 0x000000550105070c 0x00000015404141c3 0xe011f1fff71f1f1d 0xf8047c7ffdc7c7c7

def z906 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xc011f1fff41f1f1c 0xb0047c7ffd07c7c7

def z907 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xbfeec0000ffffc03 0x6ffbb00003ffff00

def z908 : W := mkw 0x0c99200000000000 0x0326480000000000 0xdf11f1fff0000001 0xf7c47c7ffc000000

def z909 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0fecffccfffffff 0xf83fb3ff33ffffff

def z910 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xfffffffff80003e3 0xfffffffffe0000f8

def z911 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x5ff00ff00bfc03fe 0x57fc03fc02ff00ff

def z912 : W := mkw 0xa066f6ccc36b6b60 0x2819bdb330dadad8 0xe0eefecccbe3e3e3 0x783bbfb332f8f8f8

def z913 : W := mkw 0x2066868c80616160 0x0819a1a320185858 0x80ee0e0c08e3e0e2 0x203b83830238f838

def z914 : W := mkw 0x0d9950000e9a9800 0x0366540003a6a600 0xbffff0000ffffc03 0xeffffc0003ffff00

def z915 : W := mkw 0x206686ccc1616360 0x0819a1b3305858d8 0x00ee0e0008e0e3e2 0x003b8380023838f8

def z916 : W := mkw 0x0eb92da220000000 0x43ae4b6888000000 0xdff1fffff0000003 0xf7fc7ffffc000000

def z917 : W := mkw 0x9fffafaaacd0f0b0 0x67ffebeaab343c2c 0x1fee0e0008e0e0e2 0x07fb838002383838

def z918 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff0fcfcfcc03ffff 0xffc3f3f3f300ffff

def z919 : W := mkw 0x4bb00df00db492d8 0x12ec037c036d24b6 0x7ff00ff00fffffff 0xdffc03fc03ffffff

def z920 : W := mkw 0x0890000000000000 0x0224000000000000 0xdff1f1fff0000003 0xf7fc7c7ffc000000

def z921 : W := mkw 0x5f9959775f9f9f9e 0x17e6565dd7e7e7e7 0xff11f1fff71f1f1d 0xffc47c7ffdc7c7c7

def z922 : W := mkw 0x00005015520f0d0e 0x000014055483c343 0xc011f1fff41f1c1d 0xf0047c7ffd07c707

def z923 : W := mkw 0x2066868c80616160 0x0819a1a320185858 0x40ee0e0c08e0e3e2 0x103b8383023838f8

def z924 : W := mkw 0x4effafaaa0b00040 0x53bfebeaa82c0010 0xdffffffff0e00003 0xf7fffffffc380000

def z925 : W := mkw 0x2066868c80616160 0x0819a1a320185858 0x20ee0e0008e3e3e2 0x083b83800238f8f8

def z926 : W := mkw 0x2066c6dcd367636a 0x0819b1b734d9d8da 0xe0eecefcfbe3e3e3 0x783bb3bf3ef8f8f8

def z927 : W := mkw 0x4bb00df0adb402d8 0x52ec037c2b6d00b6 0x7ff00ff0fffc03ff 0xdffc03fc3fff00ff

def z928 : W := mkw 0x002256dd532f2f6e 0x000895b754cbcbdb 0xe0ffffffffffffff 0xf83fffffffffffff

def z929 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xbfef00000ffffc03 0xaffbc00003ffff00

def z930 : W := mkw 0x00005011120e0c0e 0x0000140444838303 0xe011f1fff71f1c1d 0xf8047c7ffdc7c707

def z931 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0xfff1fff00ffc03ff 0xfffc7ffc03ff00ff

def z932 : W := mkw 0x006484c001604240 0x0019213000581090 0x60ee0ec00be0e3e3 0x583b83b002f838f8

def z933 : W := mkw 0x150b020d0c01b5b4 0x0542c08343006d6d 0xff0f0e0c0c03ffff 0xbfc3c3830300ffff

def z934 : W := mkw 0x2066c68cc2636160 0x0819b1a33098d858 0x00ee0e0008e3e0e2 0x003b83800238f838

def z935 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0fffecccfffffff 0xf83fffb333ffffff

def z936 : W := mkw 0x6bb00df0cdb402d8 0x1aec037c336d00b6 0x7ff00ff0cffc03ff 0xdffc03fc33ff00ff

def z937 : W := mkw 0x00005055530f0f0e 0x0000141554c3c3c3 0xe0f1f1ffffff1f1f 0xf83c7c7fffffc7c7

def z938 : W := mkw 0x2066d6ccc36b6b60 0x0819b5b330dadad8 0xe0eececccfffffe3 0x783bb3b333fffff8

def z939 : W := mkw 0x066f8f8a80000000 0x019be3e2a0000000 0xdffffffff0000003 0xf7fffffffc000000

def z940 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x20ee0e000be0e0e3 0x483b838002f83838

def z941 : W := mkw 0x2046c20cc2436120 0x0811b0833090d848 0xe0eece0ccbe3e3e3 0x783bb38332f8f8f8

def z942 : W := mkw 0x0af4ada0a0000000 0x42bd2b6828000000 0xdff1fffff0000003 0xf7fc7ffffc000000

def z943 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0eecfcccfe3e3ff 0xf83bb3f333f8f8ff

def z944 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff1f0f0f0f1fffff 0xffc7c3c3c3c7ffff

def z945 : W := mkw 0x89d4d0000edad800 0x2275340003b6b600 0xbffec0000ffffc03 0xefffb00003ffff00

def z946 : W := mkw 0x0ebb2faaa0000000 0x43aecbeaa8000000 0xdf11fffff0000001 0xf7c47ffffc000000

def z947 : W := mkw 0x944ff20fa24bfd24 0x6513fc83e892ff49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z948 : W := mkw 0x2effafaaa0202060 0x4bbfebeaa8080818 0xdffffffff00000e3 0xf7fffffffc000038

def z949 : W := mkw 0x00001055510d0f0e 0x00000415544343c3 0xc011f1fff41c1f1d 0xf0047c7ffd0707c7

def z950 : W := mkw 0x2066d6cdd36b6f66 0x0819b5b374dadbd9 0xe0efffcfffe3ffff 0xf83bfff3fff8ffff

def z951 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0eecfffffffffff 0x783bb3ffffffffff

def z952 : W := mkw 0x344fd20fd24bfd26 0x0d13f483f492ff49 0x800ff00ff003fc00 0x2003fc03fc00ff00

def z953 : W := mkw 0x5f9909220c909090 0x17e6424883242424 0x1f00000000000000 0x07c0000000000000

def z954 : W := mkw 0xc8f4f4f053fe4a4a 0x323d3d3c14ff9292 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z955 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xfffff1000fffff1f 0xfffffc4003ffffc7

def z956 : W := mkw 0x206686ccc1616360 0x0819a1b3305858d8 0xe0ee0eccc8e3e3e3 0x383b83b33238f8f8

def z957 : W := mkw 0x006686cc81212360 0x0019a1b3204848d8 0xe0eececccbe3e3e3 0x783bb3b332f8f8f8

def z958 : W := mkw 0x00001051110c0e0e 0x0000041444430383 0xe011f1fff71c1f1d 0xf8047c7ffdc707c7

def z959 : W := mkw 0x160b0b0f0001b5b4 0x0582c2c3c0006d6d 0xdf0f0f0f0003ffff 0xb7c3c3c3c000ffff

def z960 : W := mkw 0x2066d6ccc36b6b60 0x0819b5b330dadad8 0xe0ffffffffffffe3 0xf83ffffffffffff8

def z961 : W := mkw 0x2066c68882626060 0x0819b1a220989818 0x80eece0008e3e0e2 0x203bb3800238f838

def z962 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff0e0e0c0c03ffff 0x3fc383830300ffff

def z963 : W := mkw 0x206686ccc1616360 0x0819a1b3305858d8 0x60ee0ecccbe0e3e3 0x583b83b332f838f8

def z964 : W := mkw 0x2066c68882626060 0x0819b1a220989818 0x00eece000be0e0e2 0x403bb38002f83838

def z965 : W := mkw 0x0046c24c43436320 0x0011b09310d0d8c8 0xe0eececccbe3e3e3 0x783bb3b332f8f8f8

def z966 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x9ffff1fff0000000 0xe7fffc7ffc000000

def z967 : W := mkw 0x2066d688826a6860 0x0819b5a2209a9a18 0xa0fffe000ffffce3 0xe83fff8003ffff38

def z968 : W := mkw 0x066fafaaa0000000 0x419bebeaa8000000 0xdf0ffffff0000003 0xb7c3fffffc000000

def z969 : W := mkw 0xcf9939200c989890 0x33e64e4803262624 0x1f113000041c1c00 0x87c44c0001070700

def z970 : W := mkw 0x2066d6ccc36b6b60 0x0819b5b330dadad8 0xe0fefecccbffe3e3 0x783fbfb332fff8f8

def z971 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x7ff0fff0fffc03ff 0xdffc3ffc3fff00ff

def z972 : W := mkw 0x2066c6dcc3676368 0x0819b1b730d9d8da 0xe0eececccfffe3ff 0x783bb3b333fff8ff

def z973 : W := mkw 0x1effafaaa000b020 0x47bfebeaa8002c08 0xdffffffff000e003 0xf7fffffffc003800

def z974 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0fefefcffffffff 0x783fbfbf3fffffff

def z975 : W := mkw 0x0effafaaa0009000 0x43bfebeaa8002400 0xdffffffff003fc03 0xf7fffffffc00ff00

def z976 : W := mkw 0x00005050030e0a08 0x0000141400c38282 0xe011f1fff71f1f1d 0xf8047c7ffdc7c7c7

def z977 : W := mkw 0xcfffafaaacf0d0d0 0x73ffebeaab3c3434 0x1fee0e0008e0e0e2 0x07fb838002383838

def z978 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0effecfffffffff 0x783bffb3ffffffff

def z979 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff1fff0f0c03ffff 0xffc7ffc3c300ffff

def z980 : W := mkw 0x5f9909320c949098 0x17e6424c83252426 0x1f100130041c001c 0x87c4004c01070007

def z981 : W := mkw 0x00005051530e0e0e 0x0000141454c38383 0xc011f1fff71c1c1d 0xf0047c7ffdc70707

def z982 : W := mkw 0x9f9939020c989890 0x27e64e4083262624 0x1f113000041c1c00 0x87c44c0001070700

def z983 : W := mkw 0x0bb00da00c900090 0x02ec036803240024 0x7ff00ff00ffc03ff 0xdffc03fc03ff00ff

def z984 : W := mkw 0x4b9009500db402d8 0x12e40254036d00b6 0x7ff00f000ffc03ff 0xdffc03c003ff00ff

def z985 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xbfeff0000ffffc02 0x2ffbfc0003ffff00

def z986 : W := mkw 0x206686c881606260 0x0819a1b220581898 0xe0eececccbe0e3e3 0x783bb3b332f838f8

def z987 : W := mkw 0x370b0b0fcc01b5b4 0x0dc2c2c3f3006d6d 0xff0f0f0fcc03ffff 0xbfc3c3c3f300ffff

def z988 : W := mkw 0x0effafaaa0000090 0x43bfebeaa8000024 0xdffffffff00003ff 0xf7fffffffc0000ff

def z989 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0fefffffbffe3ff 0x783fbffffefff8ff

def z990 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xffef0f0f0fe3ffff 0xfffbc3c3c3f8ffff

def z991 : W := mkw 0x170909030c009494 0x05c24240c3002525 0xff0f0f030c03ffff 0xbfc3c3c0c300ffff

def z992 : W := mkw 0x4bb02df02db402d8 0x52ec0b7c0b6d00b6 0x7ff03ff03ffc03ff 0xdffc0ffc0fff00ff

def z993 : W := mkw 0x4b9009300c940098 0x12e4024c03250026 0x7ff00f300ffc03ff 0xdffc03cc03ff00ff

def z994 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xbffff0f0fffffc03 0xeffffc3c3fffff00

def z995 : W := mkw 0x2066c6c8c3626260 0x0819b1b230d89898 0xc0eececccbe0e0e3 0x703bb3b332f83838

def z996 : W := mkw 0x8d9950000edad800 0x2366540003b6b600 0xbfff00000ffffc03 0xefffc00003ffff00

def z997 : W := mkw 0x010050555f9f0f0e 0x0040141557e7c3c3 0x200000000fff1f1c 0x0800000003ffc7c7

def z998 : W := mkw 0x2066c6c8c3626260 0x0819b1b230d89898 0xa0eecec0cbe3e0e3 0x683bb3b032f8f838

def z999 : W := mkw 0x0dddc0000ed2d000 0x0377700003b4b400 0xbfffc0000ffffc03 0xeffff00003ffff00

def z1000 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xfffff0cccffffc03 0xfffffc3333ffff00

def z1001 : W := mkw 0x0ab20faaa0000000 0x42ac83eaa8000000 0xdff1fffff0000003 0xf7fc7ffffc000000

def z1002 : W := mkw 0x0064848000604040 0x0019212000181010 0x00ee0e0008e0e0e2 0x003b838002383838

def z1003 : W := mkw 0x2064c4c443636360 0x0819313110d8d8d8 0xe0eecec00be3e3e3 0x783bb3b002f8f8f8

def z1004 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xff0fff0ffc03ffff 0xbfc3ffc3ff00ffff

def z1005 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0fecffccbe3e3e3 0xf83fb3ff32f8f8f8

def z1006 : W := mkw 0x2066c68882626060 0x0819b1a220989818 0xe0eececccbe3e0e3 0x783bb3b332f8f838

def z1007 : W := mkw 0x2066c6c8c3626260 0x0819b1b230d89898 0x60eecec0cbe0e3e3 0x583bb3b032f838f8

def z1008 : W := mkw 0x1effafaaa00020b0 0x47bfebeaa800082c 0xdffffffff00000e3 0xf7fffffffc000038

def z1009 : W := mkw 0xcf9939322c9c9898 0x73e64e4c8b272626 0x1f113133341c1c1c 0x87c44c4ccd070707

def z1010 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0efcfcfcbe3e3e3 0xf83bf3f3f2f8f8f8

def z1011 : W := mkw 0x2066d6cdd36b6f66 0x0819b5b374dadbd9 0xe0fffffffbe3ffe3 0xf83ffffffef8fff8

def z1012 : W := mkw 0x002206c801202260 0x000881b200480898 0x60ee0ec00be0e3e3 0x583b83b002f838f8

def z1013 : W := mkw 0x2066c6ddd367676e 0x0819b1b774d9d9db 0xe0efcfffffe3ffff 0xf83bf3fffff8ffff

def z1014 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x3ffe00000ffffc03 0xcfff800003ffff00

def z1015 : W := mkw 0x0046820c00416120 0x0011a08300105848 0xe0ee0e0c08e3e3e3 0x383b83830238f8f8

def z1016 : W := mkw 0x002206dd0125276c 0x000881b7404949db 0xe0ff0fff0fffffff 0xf83fc3ffc3ffffff

def z1017 : W := mkw 0x8dddf000aedad800 0x63777c002bb6b600 0xbffff000fffffc03 0xeffffc003fffff00

def z1018 : W := mkw 0xb44ff20fc24bfd24 0x2d13fc83f092ff49 0x800ff00fc003fc00 0x2003fc03f000ff00

def z1019 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0x60ee0ecccbe3e3e2 0x183b83b332f8f8f8

def z1020 : W := mkw 0x62220ffdd12527fe 0x188883ff744949ff 0x40000ffff00003fc 0x100003fffc0000ff

def z1021 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x7ff13ff33ffc03ff 0xdffc4ffccfff00ff

def z1022 : W := mkw 0x0cffa6aaa0000000 0x433fe9aaa8000000 0x9ffff0fff0000003 0xe7fffc3ffc000000

def z1023 : W := mkw 0x4f9909300c949098 0x13e6424c03252426 0x1f110130041c1c1c 0x87c4404c01070707

def z1024 : W := mkw 0x2066c6ddd367676e 0x0819b1b774d9d9db 0xe0eececccbe3e3ff 0x783bb3b332f8f8ff

def z1025 : W := mkw 0x910050555fdfffbe 0x2440141557f7ffef 0x200000000ffffffc 0x0800000003ffffff

def z1026 : W := mkw 0x32220fdfd12527fe 0x0c8883f7f44949ff 0x40000ffff00003fc 0x100003fffc0000ff

def z1027 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x80eece0cc8e0e0e2 0x203bb38332383838

def z1028 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0x3f0f0f030c03fffe 0x8fc3c3c0c300ffff

def z1029 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0fffecccbe3e3e3 0xf83fffb332f8f8f8

def z1030 : W := mkw 0x03020b0d0c0125b4 0x00c082c34300496d 0xff0f0f0f0c03ffff 0xbfc3c3c3c300ffff

def z1031 : W := mkw 0x2066c6dcc3676368 0x0819b1b730d9d8da 0xe0fecefccbffe3e3 0x783fb3bf32fff8f8

def z1032 : W := mkw 0x2066868880606060 0x0819a1a220181818 0xc0ee0e0c08e0e0e3 0x303b838302383838

def z1033 : W := mkw 0x2064c4c0c3624240 0x0819313030d89090 0xe0eecec0cbe3e3e3 0x783bb3b032f8f8f8

def z1034 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0x5ffefffff0000002 0x57ffbffffc000000

def z1035 : W := mkw 0x2066d6ddd36f6f6e 0x0819b5b774dbdbdb 0xe0fffefffbffffe3 0x783fffbffefffff8

def z1036 : W := mkw 0x2066868880606060 0x0819a1a220181818 0xa0ee0e0008e3e0e3 0x283b83800238f838

def z1037 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x00eecec0c8e0e0e2 0x403bb3b032383838

def z1038 : W := mkw 0x2066c68c82636160 0x0819b1a32098d858 0xe0eece0c0be3e3e3 0x783bb38302f8f8f8

def z1039 : W := mkw 0x170b0b0a0c00b0b0 0x05c2c2c283002c2c 0xff0f0f000c03ffff 0xbfc3c3c00300ffff

def z1040 : W := mkw 0x0af6afaaa0000000 0x42bdabeaa8000000 0x5ff0fffff0000003 0xd7fc3ffffc000000

def z1041 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x40ee0ec008e0e0e3 0x503b83b002383838

def z1042 : W := mkw 0x5f9929332c94949c 0x57e64a4ccb252527 0x1f113133341c1c1c 0x87c44c4ccd070707

def z1043 : W := mkw 0x00005055534f4f0e 0x0000141554d3d3c3 0xe011f1ffffffff1d 0xf8047c7fffffffc7

def z1044 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x5ff00ff007fc03fc 0xd7fc03fc01ff00ff

def z1045 : W := mkw 0x8cddf00002dad800 0x23377c0000b6b600 0x9ffff00003fffc03 0xe7fffc0000ffff00

def z1046 : W := mkw 0x2066c6ddd367676e 0x0819b1b774d9d9db 0xe0fffffffbe3e3ff 0xf83ffffffef8f8ff

def z1047 : W := mkw 0x2066868880606060 0x0819a1a220181818 0x60ee0e0008e0e3e3 0x183b8380023838f8

def z1048 : W := mkw 0x410050555f9f0f9e 0x1040141557e7c3e7 0x20000000071f1f1c 0x0800000001c7c7c7

def z1049 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0eecffffbe3e3e3 0x783bb3fffef8f8f8

def z1050 : W := mkw 0x0409000000000000 0x0102400000000000 0xdf1ff1fff0000003 0xf7c7fc7ffc000000

def z1051 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xfffff10f0ffffc03 0xfffffc43c3ffff00

def z1052 : W := mkw 0x5fffafaaacb0b0f0 0x57ffebeaab2c2c3c 0x1fee0e0008e0e0e2 0x07fb838002383838

def z1053 : W := mkw 0x002004c001200240 0x0008013000480090 0xe0ee0ec00be3e3e3 0x783b83b002f8f8f8

def z1054 : W := mkw 0x2066d6cdc36b6f64 0x0819b5b370dadbd9 0xe0ffffcfcfffffff 0xf83ffff3f3ffffff

def z1055 : W := mkw 0x6066c6fcc3676368 0x1819b1bf30d9d8da 0xe0eecefccbe3e3e3 0x783bb3bf32f8f8f8

def z1056 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xfffff1f00ffffc03 0xfffffc7c03ffff00

def z1057 : W := mkw 0x8dddf0202edad800 0x63777c080bb6b600 0xbffff0303ffffc03 0xeffffc0c0fffff00

def z1058 : W := mkw 0x170b0b0f0c01b5b4 0x05c2c2c3c3006d6d 0xdf0f0f0f0403fffc 0xb7c3c3c3c100ffff

def z1059 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x7fe00ec00ffc03ff 0x5ff803b003ff00ff

def z1060 : W := mkw 0x52220fff512527fe 0x148883ffd44949ff 0x40000ffff00003fc 0x100003fffc0000ff

def z1061 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x9ffff00007fffc00 0xe7fffc0001ffff00

def z1062 : W := mkw 0x4ab00df001b402d8 0x12ac037c006d00b6 0x5ff00ff003fc03ff 0xd7fc03fc00ff00ff

def z1063 : W := mkw 0x202206ccc1212360 0x080881b3304848d8 0xe0ee0ecccbe3e3e3 0x783b83b332f8f8f8

def z1064 : W := mkw 0x8dddf0000edad890 0x23777c0003b6b624 0xbffff0000fffffff 0xeffffc0003ffffff

def z1065 : W := mkw 0x206686c881606260 0x0819a1b220581898 0x00ee0ec00be0e0e2 0x403b83b002f83838

def z1066 : W := mkw 0x2066c6ccc3636360 0x0819b1b330d8d8d8 0xe0effecffbe3e3e3 0x783bffb3fef8f8f8

def z1067 : W := mkw 0xdf9939330c9c9c9c 0x37e64e4cc3272727 0x1f113133041c1c1c 0x87c44c4cc1070707

def z1068 : W := mkw 0x206686c881606260 0x0819a1b220581898 0x20ee0e000be0e3e2 0x083b838002f838f8

def z1069 : W := mkw 0x0022068800202060 0x000881a200080818 0x00ee0e0008e0e0e2 0x003b838002383838

def z1070 : W := mkw 0x206686c881606260 0x0819a1b220581898 0x40ee0ec008e0e3e2 0x103b83b0023838f8

def z1071 : W := mkw 0x4bb00df00db402d8 0x12ec037c036d00b6 0x7fe00ff00ffc03fe 0x1ff803fc03ff00ff

def z1072 : W := mkw 0x510050555fbfbffe 0x1440141557efefff 0x200000000ffffffc 0x0800000003ffffff

def z1073 : W := mkw 0x43200dd00db402d8 0x10c80374036d00b6 0x7fe00fc00ffc03ff 0xdff803f003ff00ff

def z1074 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0xbffff00ffffffc03 0xeffffc03ffffff00

def z1075 : W := mkw 0x010050555f0f9f0e 0x0040141557c3e7c3 0x200000000f1fff1c 0x0800000003c7ffc7

def z1076 : W := mkw 0x2066c6c8c3626260 0x0819b1b230d89898 0x00ee0e000be0e0e2 0x003b838002f83838

def z1077 : W := mkw 0x13020b0d0c01b5b4 0x04c082c343006d6d 0xff0e0f0c0c03ffff 0xbfc383c30300ffff

def z1078 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xfffffffff803e003 0xfffffffffe00f800

def z1079 : W := mkw 0xadddf000cedad800 0x2b777c0033b6b600 0xbffff000cffffc03 0xeffffc0033ffff00

def z1080 : W := mkw 0x8dddf0000edad800 0x23777c0003b6b600 0x3fff30000ffffc02 0x8fffcc0003ffff00

def z1081 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xfffffffff400031f 0xfffffffffd0000c7

def z1082 : W := mkw 0x170b0b2f2c01b5b4 0x45c2c2cbcb006d6d 0xff0f0f3f3c03ffff 0xbfc3c3cfcf00ffff

def z1083 : W := mkw 0x0064c4c443634340 0x0019313110d8d0d0 0xe0eececccbe3e3e3 0x783bb3b332f8f8f8

def z1084 : W := mkw 0x9f9929030c909494 0x27e64a40c3242525 0x1f01010304001c1c 0x87c04040c1000707

def z1085 : W := mkw 0x8d9930000c989800 0x23664c0003262600 0xbfff30000ffffc03 0xefffcc0003ffff00

def z1086 : W := mkw 0x0effafaaa0000000 0x43bfebeaa8000000 0xdf1ffffff0000000 0xb7c7fffffc000000

def z1087 : W := mkw 0x4bb00df05db402da 0x12ec037c176d00b6 0x7ff00ff0fffc03ff 0xdffc03fc3fff00ff

def z1088 : W := mkw 0x2066c6dcc3676368 0x0819b1b730d9d8da 0xe0ffffffffffe3ff 0xf83ffffffffff8ff

def z1089 : W := mkw 0x2066c68882626060 0x0819b1a220989818 0x20ee0e000be3e0e2 0x083b838002f8f838

def z1090 : W := mkw 0xc8f4f4f0a3fe4a48 0x723d3d3c28ff9292 0x00f0f0f0f3fc0000 0x403c3c3c3cff0000

def z1091 : W := mkw 0x0046d25d534f6f2e 0x0011b49754d3dbcb 0xe0ffffffffffffff 0xf83fffffffffffff

def z1092 : W := mkw 0x0ddda0000c909000 0x0377680003242400 0xbffff0000ffffc03 0xeffffc0003ffff00

def z1093 : W := mkw 0x2066868d80616564 0x0819a1a360185959 0xe0ef0f0f0ce3ffff 0xb83bc3c3c338ffff

def z1094 : W := mkw 0x2066868cc0616160 0x0819a1a330185858 0x00ee0e0cc8e0e0e2 0x003b838332383838

def z1095 : W := mkw 0x8effafaaa0d04000 0x63bfebeaa8341000 0xdffffffff0e00003 0xf7fffffffc380000

def z1096 : W := mkw 0x0066c68c82436120 0x0019b1a32090d848 0xe0eececccbe3e3e3 0x783bb3b332f8f8f8

def z1097 : W := mkw 0x2066d6dcd36f6b6a 0x0819b5b734dbdada 0xe0eececccbffe3e3 0x783bb3b332fff8f8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z6,z7,z5]),(0,[z0,z1,z2,z8,z4,z9,z5]),(0,[z0,z1,z2,z6,z10,z4,z5]),(0,[z0,z11,z1,z2,z6,z4,z5])],[(0,[z0,z12,z1,z2,z6,z4,z5]),(0,[z13,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z14,z6,z4,z5]),(0,[z0,z15,z16,z1,z2,z4,z5])],[(0,[z0,z1,z17,z2,z6,z4,z5]),(0,[z0,z18,z1,z2,z19,z4,z5]),(0,[z0,z20,z1,z2,z19,z4,z5]),(0,[z0,z1,z21,z2,z6,z4,z5])],[(0,[z0,z1,z2,z8,z4,z22,z5]),(0,[z0,z1,z23,z2,z8,z4,z5]),(0,[z0,z1,z2,z24,z6,z4,z5]),(0,[z0,z25,z1,z2,z6,z4,z5]),(0,[z26,z0,z1,z2,z6,z4,z5])],[(0,[z27,z0,z1,z2,z6,z4,z22]),(0,[z0,z1,z2,z6,z4,z22,z28]),(0,[z0,z1,z2,z29,z6,z4,z5]),(0,[z0,z1,z2,z30,z6,z4,z5])],[(1,[z0,z1,z2,z31,z4,z5]),(0,[z32,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z33,z5]),(0,[z0,z34,z1,z2,z6,z4,z5]),(0,[z0,z35,z1,z2,z6,z4,z5])],[(0,[z0,z1,z36,z2,z19,z4,z5]),(0,[z0,z1,z2,z37,z6,z4,z5]),(0,[z0,z1,z2,z38,z6,z4,z5])],[(0,[z39,z0,z1,z2,z6,z4,z5]),(0,[z0,z15,z1,z2,z8,z4,z5]),(0,[z0,z40,z1,z2,z19,z4,z5])]],
   [[(0,[z0,z1,z41,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z42,z5]),(0,[z43,z0,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z19,z44,z4,z5]),(0,[z0,z45,z1,z36,z6,z4,z5]),(0,[z0,z1,z46,z2,z6,z4,z5]),(0,[z0,z47,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z48,z5])],[(0,[z0,z49,z1,z2,z8,z4,z5]),(0,[z50,z0,z1,z2,z19,z4,z5])],[(0,[z0,z1,z2,z51,z6,z4,z5]),(0,[z52,z0,z2,z6,z4,z53,z5]),(0,[z54,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z19,z4,z5,z28]),(0,[z0,z1,z2,z6,z55,z4,z5]),(0,[z1,z2,z56,z57,z6,z4,z5]),(0,[z0,z2,z6,z58,z4,z59,z5]),(0,[z0,z60,z1,z2,z6,z4,z5])],[(0,[z61,z62,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z19,z4,z59,z5]),(0,[z0,z1,z2,z6,z4,z63,z5]),(0,[z0,z1,z64,z65,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z66,z5])],[(0,[z0,z67,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z19,z68,z4,z5]),(0,[z0,z1,z2,z6,z4,z69,z5]),(0,[z0,z70,z1,z2,z6,z4,z71]),(0,[z0,z1,z72,z2,z6,z4,z5])],[(0,[z73,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z74]),(0,[z0,z75,z1,z2,z6,z4,z5]),(0,[z0,z1,z76,z2,z6,z4,z5]),(0,[z0,z1,z2,z77,z6,z4,z5])],[(0,[z0,z78,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z4,z5,z79]),(0,[z0,z1,z2,z6,z80,z4,z5]),(0,[z0,z1,z81,z2,z6,z4,z5])],[(0,[z61,z0,z82,z2,z6,z4,z5]),(0,[z83,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z58,z4,z5]),(0,[z0,z84,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z85,z5]),(0,[z0,z1,z23,z2,z6,z86,z5])]],
   [[(0,[z87,z0,z1,z2,z6,z4,z5]),(0,[z0,z88,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z89,z6,z4,z5]),(0,[z0,z1,z2,z90,z6,z4,z5]),(1,[z0,z1,z2,z91,z4,z48])],[(0,[z61,z0,z92,z2,z6,z4,z5]),(0,[z0,z93,z1,z2,z6,z4,z5]),(0,[z0,z94,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z95]),(0,[z0,z96,z1,z2,z6,z4,z5]),(0,[z0,z97,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z98,z6,z4,z5]),(0,[z0,z20,z1,z2,z99,z4,z5]),(0,[z0,z1,z2,z6,z100,z4,z5]),(0,[z0,z101,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z102,z4,z5]),(0,[z0,z103,z1,z2,z4,z5,z104])],[(0,[z0,z15,z1,z2,z4,z48,z5]),(1,[z0,z1,z2,z6,z105,z86]),(0,[z0,z1,z2,z6,z4,z5,z106])],[(0,[z52,z0,z107,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z108,z4,z5]),(0,[z1,z2,z19,z6,z8,z4,z5]),(0,[z0,z1,z2,z91,z19,z4,z5]),(0,[z0,z92,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z109,z5]),(0,[z110,z0,z1,z2,z6,z4,z5]),(0,[z111,z0,z1,z2,z6,z4,z5])],[(1,[z0,z1,z112,z6,z4,z5]),(0,[z62,z0,z1,z2,z6,z4,z5]),(0,[z0,z113,z1,z2,z6,z4,z5]),(0,[z0,z114,z1,z2,z6,z4,z5]),(0,[z0,z115,z1,z2,z6,z4,z5])],[(1,[z61,z1,z2,z8,z4,z5]),(0,[z0,z116,z1,z2,z6,z4,z5]),(0,[z117,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z65,z8,z4,z5]),(0,[z0,z82,z2,z6,z4,z5,z28]),(0,[z0,z118,z1,z2,z6,z4,z5]),(1,[z0,z119,z1,z2,z4,z5]),(0,[z0,z119,z1,z2,z6,z4,z5])],[(0,[z61,z0,z2,z6,z58,z4,z5]),(1,[z0,z2,z6,z120,z4,z5]),(0,[z0,z1,z2,z6,z4,z121,z71]),(0,[z122,z0,z1,z2,z6,z4,z5]),(1,[z0,z123,z1,z6,z4,z5])]],
   [[(0,[z0,z124,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z8,z4,z5,z125]),(0,[z27,z1,z2,z6,z4,z22,z5]),(0,[z0,z1,z2,z6,z4,z5,z126]),(1,[z0,z40,z2,z6,z58,z5]),(0,[z0,z1,z127,z2,z6,z4,z5])],[(0,[z0,z128,z1,z2,z6,z4,z5]),(0,[z0,z129,z1,z2,z6,z4,z5]),(0,[z0,z130,z1,z2,z6,z4,z5]),(0,[z0,z131,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z132,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z133,z5]),(0,[z0,z1,z2,z6,z4,z134,z5]),(0,[z0,z1,z2,z6,z4,z135,z5])],[(0,[z136,z0,z1,z2,z137,z4,z5]),(0,[z0,z1,z2,z6,z138,z4,z5]),(0,[z0,z1,z2,z19,z4,z5,z139]),(0,[z0,z1,z2,z6,z9,z59,z5]),(0,[z0,z1,z140,z2,z6,z4,z5]),(0,[z0,z84,z15,z1,z2,z4,z5])],[(0,[z0,z141,z1,z2,z6,z4,z5]),(0,[z0,z142,z1,z2,z6,z4,z5]),(0,[z0,z143,z1,z2,z6,z4,z5]),(0,[z0,z144,z1,z2,z6,z4,z5]),(1,[z0,z1,z2,z4,z5,z145])],[(0,[z0,z1,z2,z6,z4,z146,z5]),(0,[z0,z1,z2,z6,z147,z4,z5]),(0,[z0,z148,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z5,z149,z79]),(0,[z0,z1,z2,z6,z150,z4,z5]),(0,[z0,z1,z2,z6,z151,z4,z5])],[(0,[z52,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z152]),(0,[z0,z1,z2,z153,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z154])],[(0,[z0,z155,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z156,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z149]),(0,[z0,z1,z157,z2,z6,z4,z5]),(0,[z0,z1,z2,z158,z6,z4,z5])],[(0,[z0,z82,z1,z2,z8,z4,z5]),(0,[z0,z159,z1,z2,z19,z4,z5]),(1,[z0,z160,z2,z6,z4,z5]),(0,[z0,z161,z1,z2,z6,z4,z5]),(0,[z0,z162,z1,z2,z6,z4,z5]),(0,[z0,z163,z1,z2,z6,z4,z5]),(0,[z0,z164,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z165])]],
   [[(0,[z166,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z167,z4,z5]),(0,[z0,z1,z64,z2,z8,z4,z5]),(0,[z168,z0,z1,z2,z6,z4,z5]),(1,[z0,z128,z2,z6,z4,z5]),(0,[z0,z1,z169,z2,z6,z4,z5]),(0,[z0,z20,z1,z2,z56,z4,z5]),(0,[z0,z40,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z170,z5]),(0,[z0,z1,z2,z6,z4,z171,z5])],[(0,[z0,z1,z172,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z173,z4,z5]),(0,[z0,z1,z2,z8,z4,z71,z5]),(0,[z0,z174,z1,z2,z6,z4,z5]),(1,[z0,z1,z2,z4,z5,z175]),(1,[z0,z1,z2,z176,z177,z5])],[(0,[z73,z0,z1,z178,z6,z4,z5]),(0,[z0,z1,z179,z2,z6,z4,z5]),(0,[z0,z1,z2,z180,z6,z4,z5]),(0,[z43,z1,z2,z6,z68,z4,z5]),(0,[z181,z0,z1,z2,z6,z4,z5]),(0,[z0,z47,z182,z1,z2,z6,z4]),(0,[z0,z1,z2,z6,z4,z183,z5]),(0,[z0,z1,z2,z6,z4,z184,z5])],[(0,[z0,z1,z2,z19,z4,z5,z185]),(1,[z0,z1,z2,z186,z4,z5]),(0,[z0,z1,z187,z2,z6,z4,z5]),(0,[z0,z188,z1,z2,z6,z4,z5]),(0,[z0,z189,z1,z2,z6,z4,z5]),(0,[z0,z190,z1,z2,z6,z4,z5]),(0,[z0,z191,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z192,z5]),(0,[z0,z193,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z194,z5])],[(0,[z61,z0,z1,z2,z19,z4,z5])],[(0,[z0,z1,z2,z19,z4,z5,z195]),(0,[z0,z1,z2,z6,z4,z196,z5]),(0,[z0,z1,z2,z6,z4,z5,z197]),(0,[z0,z20,z2,z6,z99,z4,z5])],[(1,[z0,z198,z2,z6,z4,z53]),(0,[z0,z1,z2,z6,z4,z5,z199]),(0,[z0,z1,z2,z6,z4,z86,z5]),(0,[z0,z1,z2,z200,z6,z4,z5])]],
   [[(1,[z0,z1,z2,z201,z4,z5]),(0,[z52,z0,z2,z6,z99,z4,z5]),(0,[z73,z0,z1,z2,z202,z4,z5]),(0,[z0,z1,z2,z6,z4,z203,z5]),(0,[z0,z204,z1,z2,z6,z4,z5]),(0,[z0,z84,z1,z2,z6,z4,z5])],[(0,[z205,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z206,z6,z4,z5]),(0,[z0,z207,z1,z36,z6,z4,z5]),(0,[z0,z1,z6,z208,z4,z209,z5]),(0,[z0,z1,z2,z177,z4,z210,z5])],[(0,[z0,z1,z2,z176,z8,z4,z5]),(0,[z27,z0,z1,z2,z6,z4,z185]),(0,[z0,z130,z2,z56,z6,z4,z5]),(0,[z0,z1,z2,z6,z211,z4,z5]),(0,[z212,z0,z1,z2,z6,z4,z5])],[(0,[z61,z0,z2,z6,z4,z53,z5]),(0,[z0,z1,z213,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z214,z4,z5]),(0,[z0,z1,z215,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z216])],[(0,[z0,z1,z2,z6,z4,z5,z217]),(0,[z0,z1,z2,z6,z218,z4,z5]),(0,[z0,z1,z64,z2,z4,z48,z5]),(0,[z0,z1,z2,z219,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z220,z5]),(0,[z221,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z6,z4,z5]),(0,[z222,z0,z1,z2,z19,z4,z5]),(0,[z0,z20,z1,z2,z8,z4,z5]),(0,[z1,z2,z6,z68,z4,z9,z5]),(0,[z0,z223,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z224]),(0,[z0,z1,z2,z6,z225,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z226])],[(0,[z136,z0,z1,z172,z6,z4,z5]),(0,[z0,z36,z2,z227,z6,z4,z5])],[(0,[z0,z1,z2,z8,z177,z4,z5]),(0,[z0,z207,z1,z227,z6,z4,z5]),(0,[z0,z228,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z229,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z230])]],
   [[(0,[z231,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z19,z232,z4,z5])],[(0,[z0,z1,z36,z2,z8,z4,z5]),(0,[z0,z1,z2,z19,z4,z53,z5]),(0,[z50,z0,z1,z2,z233,z4,z5]),(0,[z0,z1,z2,z6,z234,z4,z5]),(1,[z0,z1,z2,z235,z4,z5]),(0,[z236,z0,z1,z2,z6,z4,z5])],[(0,[z0,z40,z1,z2,z8,z4,z5]),(0,[z0,z1,z237,z2,z19,z4,z5]),(0,[z238,z0,z1,z2,z6,z4,z5])],[(1,[z0,z2,z6,z239,z4,z5]),(0,[z50,z0,z1,z2,z6,z9,z5]),(0,[z0,z1,z2,z6,z240,z4,z5])],[(0,[z0,z1,z2,z6,z4,z5,z241]),(0,[z62,z222,z1,z2,z6,z4,z5]),(1,[z1,z2,z19,z8,z4,z5]),(0,[z50,z0,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z242,z5]),(0,[z0,z243,z1,z2,z6,z4,z5]),(0,[z0,z84,z16,z1,z2,z4,z5]),(0,[z0,z1,z23,z2,z6,z4,z5]),(0,[z0,z244,z1,z2,z6,z4,z5]),(0,[z0,z1,z6,z4,z5,z245,z104])],[(0,[z136,z0,z1,z2,z19,z4,z5]),(0,[z0,z182,z1,z2,z19,z4,z5]),(0,[z0,z2,z19,z6,z239,z4,z5]),(0,[z0,z15,z1,z2,z176,z4,z5])],[(0,[z246,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z247]),(0,[z0,z1,z2,z6,z4,z248,z5]),(0,[z0,z1,z2,z6,z4,z5,z249])],[(0,[z0,z2,z6,z4,z53,z5,z28]),(0,[z0,z1,z2,z6,z250,z4,z5]),(0,[z0,z75,z1,z2,z6,z208,z5]),(0,[z0,z1,z2,z6,z251,z4,z5]),(0,[z0,z16,z1,z2,z177,z4,z5])]],
   [[(0,[z0,z1,z2,z6,z252,z4,z5]),(0,[z0,z47,z1,z2,z6,z4,z79])],[(0,[z43,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z253,z5]),(0,[z0,z254,z1,z2,z6,z4,z5])],[(0,[z0,z49,z1,z2,z6,z4,z5]),(0,[z0,z84,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z255,z5]),(0,[z1,z2,z6,z4,z22,z5,z185]),(0,[z0,z1,z2,z256,z6,z4,z5])],[(0,[z136,z1,z2,z178,z6,z4,z5]),(0,[z0,z257,z2,z178,z6,z4,z5]),(0,[z0,z258,z1,z2,z8,z4,z5]),(0,[z0,z82,z1,z2,z6,z4,z53]),(0,[z259,z0,z1,z2,z6,z4,z5]),(0,[z260,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z261,z4,z5]),(0,[z0,z1,z2,z19,z4,z262,z5]),(0,[z0,z1,z2,z6,z233,z4,z5]),(0,[z43,z0,z1,z2,z263,z4,z5]),(0,[z0,z1,z2,z6,z264,z4,z5]),(0,[z0,z1,z2,z265,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z266,z5]),(0,[z0,z1,z2,z6,z267,z4,z5])],[(0,[z0,z67,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z268,z4,z5]),(0,[z0,z45,z207,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z269]),(0,[z0,z70,z1,z2,z6,z4,z5])],[(0,[z61,z0,z1,z2,z6,z4,z5]),(0,[z270,z0,z1,z2,z6,z4,z5]),(1,[z61,z107,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z271]),(0,[z0,z1,z2,z6,z272,z4,z5])],[(1,[z0,z1,z2,z273,z4,z5]),(0,[z0,z1,z2,z8,z4,z5,z28]),(0,[z0,z1,z2,z91,z8,z4,z5]),(0,[z0,z1,z2,z19,z19,z4,z5]),(1,[z274,z1,z2,z6,z4,z185]),(0,[z0,z45,z2,z227,z6,z4,z5]),(0,[z0,z1,z2,z6,z275,z4,z5]),(0,[z0,z1,z2,z6,z276,z4,z5]),(0,[z0,z1,z2,z6,z277,z4,z5]),(0,[z0,z1,z2,z6,z4,z278,z5]),(0,[z0,z75,z1,z2,z6,z71,z5]),(1,[z0,z16,z1,z2,z4,z139])]],
   [[(0,[z0,z1,z2,z8,z4,z59,z5]),(0,[z0,z1,z2,z6,z4,z279,z5])],[(0,[z0,z1,z2,z8,z68,z4,z5])],[(1,[z52,z280,z2,z6,z4,z5]),(0,[z281,z0,z1,z2,z6,z4,z5]),(0,[z0,z282,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z283,z4,z5])],[(0,[z0,z284,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z8,z285,z4,z5]),(0,[z0,z286,z1,z2,z19,z4,z5]),(1,[z43,z1,z2,z6,z68,z5]),(0,[z0,z1,z2,z6,z4,z287,z5]),(1,[z0,z1,z2,z6,z4,z121]),(0,[z0,z288,z1,z2,z6,z4,z5])],[(0,[z0,z289,z2,z6,z4,z5,z185]),(0,[z0,z1,z2,z6,z290,z4,z5]),(0,[z291,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z178,z19,z4,z5]),(0,[z292,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z293,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z294]),(0,[z0,z84,z1,z2,z4,z48,z5]),(0,[z0,z295,z1,z2,z6,z4,z5])],[(0,[z0,z296,z1,z2,z6,z4,z5]),(0,[z297,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z239,z4,z5]),(0,[z0,z1,z2,z298,z6,z4,z5]),(0,[z0,z1,z2,z65,z6,z4,z5]),(0,[z0,z1,z2,z6,z86,z5,z104])]],
   [[(0,[z1,z172,z2,z178,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z299])],[(0,[z61,z0,z2,z6,z99,z4,z5]),(0,[z0,z124,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z4,z48,z5,z139]),(0,[z0,z1,z300,z2,z6,z4,z5])],[(0,[z43,z0,z1,z2,z6,z9,z5]),(0,[z0,z1,z2,z6,z4,z301,z5]),(0,[z0,z1,z2,z302,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z303])],[(0,[z280,z1,z2,z6,z8,z4,z5]),(1,[z0,z1,z2,z137,z4,z5]),(1,[z0,z289,z2,z6,z4,z5]),(0,[z0,z1,z2,z304,z6,z4,z5]),(0,[z0,z1,z2,z91,z4,z48,z5])],[(1,[z136,z1,z178,z6,z4,z5]),(0,[z0,z1,z172,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z4,z5]),(0,[z0,z1,z2,z6,z305,z4,z5]),(1,[z1,z2,z57,z6,z4,z5]),(1,[z306,z1,z2,z6,z4,z5]),(0,[z0,z307,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z308,z5]),(0,[z0,z1,z309,z2,z6,z4,z5]),(0,[z0,z310,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z311,z6,z4,z5]),(0,[z0,z1,z2,z6,z312,z4,z5])],[(0,[z0,z1,z2,z313,z6,z4,z5]),(0,[z0,z1,z2,z8,z4,z5,z139]),(0,[z0,z45,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z19,z99,z4,z5]),(0,[z0,z314,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z315,z5]),(1,[z0,z316,z1,z2,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z317])]],
   [[(0,[z61,z0,z1,z2,z8,z4,z5]),(0,[z0,z318,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z201,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z319,z5]),(0,[z0,z1,z2,z6,z4,z320,z5]),(0,[z0,z82,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z321,z5]),(0,[z0,z47,z1,z2,z6,z105,z4])],[(0,[z0,z1,z2,z227,z19,z4,z5]),(0,[z0,z1,z2,z322,z6,z4,z5]),(0,[z0,z1,z64,z2,z6,z4,z5]),(0,[z323,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z19,z4,z209,z5]),(0,[z0,z1,z2,z19,z4,z86,z5]),(0,[z0,z324,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z5,z325])],[(0,[z27,z0,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z19,z4,z5,z104]),(0,[z0,z326,z1,z2,z6,z4,z5])],[(0,[z61,z0,z1,z17,z6,z4,z5]),(0,[z0,z123,z1,z6,z4,z5,z104])],[(0,[z61,z1,z107,z2,z6,z4,z5]),(0,[z0,z327,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z328,z5]),(0,[z0,z1,z2,z6,z4,z329,z5]),(0,[z0,z47,z1,z2,z6,z4,z209])],[(0,[z0,z1,z2,z330,z8,z4,z5]),(0,[z0,z1,z2,z8,z4,z210,z5]),(0,[z0,z1,z331,z2,z19,z4,z5]),(0,[z0,z332,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z333,z4,z5]),(0,[z0,z15,z1,z2,z6,z177,z5]),(0,[z0,z1,z2,z334,z6,z4,z5]),(0,[z0,z16,z1,z2,z4,z5,z139])]],
   [[(0,[z0,z1,z2,z6,z335,z4,z5]),(1,[z0,z1,z2,z336,z4,z5]),(0,[z222,z0,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z8,z4,z5,z185]),(0,[z0,z207,z36,z2,z6,z4,z5]),(0,[z0,z337,z1,z2,z6,z4,z5]),(0,[z338,z0,z1,z2,z6,z4,z5])],[(0,[z339,z0,z1,z2,z6,z4,z5]),(0,[z61,z0,z1,z2,z6,z4,z340]),(0,[z0,z103,z1,z2,z6,z4,z5])],[(0,[z62,z280,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z341,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z53,z22]),(0,[z0,z1,z342,z2,z6,z4,z5])],[(0,[z0,z1,z343,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z344]),(0,[z345,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z346,z6,z4,z5]),(0,[z0,z1,z2,z176,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z340,z5]),(0,[z0,z1,z2,z6,z4,z5,z347]),(0,[z0,z160,z1,z2,z6,z4,z5]),(0,[z0,z348,z1,z2,z6,z4,z5]),(0,[z0,z349,z1,z2,z6,z4,z5]),(0,[z350,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z351,z5]),(0,[z0,z1,z2,z6,z4,z5,z352])],[(0,[z0,z1,z237,z2,z8,z4,z5]),(0,[z0,z1,z2,z19,z208,z4,z5]),(0,[z0,z1,z2,z6,z4,z9,z5]),(0,[z0,z2,z6,z4,z353,z5,z185]),(0,[z0,z84,z1,z6,z232,z4,z5]),(1,[z0,z47,z1,z6,z4,z79]),(0,[z0,z15,z1,z2,z6,z210,z5]),(0,[z0,z1,z2,z6,z105,z4,z86])],[(0,[z0,z1,z2,z6,z285,z4,z5]),(0,[z0,z18,z1,z2,z6,z4,z5]),(1,[z0,z2,z19,z239,z4,z5]),(0,[z0,z20,z1,z2,z6,z4,z5]),(0,[z0,z354,z1,z2,z6,z4,z5]),(0,[z0,z1,z23,z2,z6,z208,z5]),(0,[z0,z1,z2,z6,z4,z5,z355])],[(0,[z280,z1,z107,z2,z6,z4,z5]),(0,[z0,z356,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z357,z5]),(0,[z0,z358,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z1,z2,z6,z4,z5,z359]),(0,[z136,z0,z1,z2,z8,z4,z5]),(0,[z0,z182,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z22,z5]),(0,[z360,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z91,z6,z4,z48])],[(0,[z43,z0,z1,z2,z6,z68,z5]),(0,[z0,z361,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z362,z5]),(0,[z0,z1,z363,z2,z6,z4,z5])],[(0,[z52,z280,z1,z2,z6,z4,z5]),(0,[z0,z1,z36,z2,z6,z4,z5])],[(1,[z0,z1,z2,z6,z364,z5]),(0,[z365,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z366,z5])],[(0,[z0,z1,z2,z6,z367,z4,z5]),(0,[z0,z1,z368,z2,z6,z4,z5]),(0,[z0,z75,z1,z6,z4,z209,z5])],[(0,[z0,z1,z2,z8,z232,z4,z5]),(0,[z50,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z369]),(0,[z0,z370,z1,z2,z6,z4,z5]),(0,[z0,z92,z1,z2,z6,z59,z5]),(0,[z0,z1,z371,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z372,z4,z5]),(0,[z0,z1,z373,z2,z6,z4,z5]),(1,[z0,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z8,z4,z53,z5]),(0,[z0,z1,z2,z19,z105,z4,z5]),(0,[z0,z289,z1,z2,z6,z4,z5]),(0,[z0,z1,z374,z2,z6,z4,z5]),(0,[z0,z1,z23,z2,z6,z71,z5]),(0,[z0,z1,z2,z375,z6,z4,z5])],[(0,[z0,z1,z2,z376,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z377]),(0,[z0,z1,z2,z6,z378,z4,z5]),(0,[z0,z119,z1,z2,z4,z71,z5]),(0,[z0,z1,z2,z379,z6,z4,z5])]],
   [[(0,[z0,z45,z1,z2,z6,z4,z5]),(0,[z0,z1,z380,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z381,z4,z5]),(0,[z0,z382,z1,z2,z6,z4,z5]),(0,[z383,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z384,z5]),(0,[z0,z1,z2,z6,z385,z4,z5])],[(0,[z0,z1,z2,z6,z4,z386,z5])],[(0,[z0,z1,z2,z19,z8,z4,z5]),(0,[z0,z47,z1,z6,z208,z4,z5]),(1,[z0,z387,z1,z2,z6,z5])],[(0,[z0,z1,z388,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z79])],[(0,[z0,z258,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z58,z4,z5]),(0,[z0,z1,z65,z6,z232,z4,z5])],[(0,[z389,z0,z1,z2,z6,z4,z5]),(0,[z27,z0,z1,z2,z6,z4,z5]),(0,[z390,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z391,z6,z4,z5])],[(0,[z0,z392,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z120,z4,z5]),(0,[z393,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z394,z5]),(1,[z0,z182,z1,z2,z6,z104]),(0,[z0,z182,z1,z2,z6,z5,z104])],[(0,[z0,z1,z2,z395,z6,z4,z5]),(0,[z0,z257,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z396,z5]),(0,[z0,z397,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z207,z1,z2,z19,z4,z5]),(0,[z27,z274,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z398,z6,z4,z5]),(0,[z0,z1,z2,z91,z6,z4,z5])],[(0,[z0,z1,z2,z178,z8,z4,z5]),(0,[z0,z40,z1,z2,z6,z59,z5]),(0,[z0,z1,z2,z6,z4,z5,z399]),(0,[z400,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z210,z5])],[(0,[z0,z401,z1,z2,z6,z4,z5]),(0,[z0,z402,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z403,z6,z4,z5]),(0,[z0,z1,z404,z2,z6,z4,z5]),(0,[z0,z1,z2,z4,z5,z175,z79]),(0,[z0,z405,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z406,z4,z5]),(0,[z407,z0,z1,z2,z6,z4,z5])],[(0,[z408,z0,z1,z2,z6,z4,z5]),(0,[z0,z47,z1,z237,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z5,z125]),(0,[z0,z409,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z410,z4,z5]),(0,[z0,z1,z2,z6,z411,z4,z5])],[(0,[z0,z1,z2,z19,z4,z48,z5]),(1,[z0,z75,z1,z6,z71,z5])],[(0,[z0,z1,z36,z178,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z412]),(0,[z0,z1,z2,z6,z4,z5,z413])]],
   [[(0,[z0,z1,z2,z3,z6,z4,z5]),(0,[z61,z0,z107,z2,z6,z4,z5]),(0,[z0,z1,z414,z2,z6,z4,z5]),(0,[z0,z16,z1,z64,z2,z4,z5]),(0,[z0,z75,z47,z1,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z5,z415]),(0,[z52,z0,z280,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z416]),(0,[z0,z16,z1,z2,z91,z4,z5])],[(0,[z61,z0,z1,z2,z6,z4,z241]),(0,[z0,z45,z1,z2,z8,z4,z5]),(0,[z0,z182,z1,z23,z2,z6,z5]),(0,[z0,z1,z2,z176,z6,z177,z5])],[(0,[z0,z1,z178,z227,z6,z4,z5]),(0,[z0,z159,z1,z2,z6,z4,z5]),(0,[z0,z1,z417,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z418,z5]),(0,[z0,z419,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z227,z8,z4,z5]),(0,[z0,z16,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z420]),(1,[z0,z1,z237,z6,z4,z209]),(0,[z0,z15,z1,z2,z4,z210,z5]),(0,[z0,z1,z2,z6,z4,z421,z5])],[(0,[z0,z1,z172,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z167,z4,z5]),(0,[z0,z1,z2,z6,z58,z9,z5]),(0,[z0,z1,z2,z6,z4,z422,z5]),(0,[z423,z0,z1,z2,z6,z4,z5]),(0,[z0,z182,z1,z2,z6,z105,z5])],[(0,[z424,z0,z1,z2,z6,z4,z5]),(0,[z306,z1,z2,z56,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z71,z5]),(1,[z0,z1,z23,z6,z208,z5]),(0,[z0,z1,z2,z6,z425,z4,z5])],[(0,[z27,z0,z1,z2,z8,z4,z5]),(0,[z0,z426,z1,z2,z6,z4,z5]),(0,[z0,z427,z1,z2,z6,z4,z5]),(0,[z0,z1,z428,z2,z6,z4,z5]),(0,[z0,z182,z1,z2,z6,z4,z104]),(0,[z0,z1,z2,z429,z6,z4,z5])]],
   [[(0,[z0,z430,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z53,z185]),(0,[z431,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z6,z208,z4,z71,z5]),(0,[z0,z1,z2,z176,z6,z210,z5])],[(0,[z0,z1,z2,z6,z4,z432,z5]),(0,[z0,z1,z2,z433,z6,z4,z5]),(0,[z0,z1,z434,z2,z6,z4,z5]),(0,[z0,z1,z2,z435,z6,z4,z5])],[(0,[z0,z1,z2,z8,z4,z436,z5]),(1,[z0,z1,z2,z263,z4,z5]),(0,[z0,z2,z56,z6,z99,z4,z5]),(0,[z0,z1,z2,z57,z6,z4,z5]),(0,[z0,z1,z2,z437,z6,z4,z5])],[(0,[z52,z0,z1,z2,z201,z4,z5]),(0,[z50,z0,z1,z2,z186,z4,z5]),(0,[z0,z1,z438,z2,z6,z4,z5])],[(0,[z0,z1,z2,z8,z99,z4,z5]),(0,[z0,z1,z2,z6,z4,z439,z5])],[(0,[z61,z1,z2,z6,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z440,z5]),(0,[z274,z0,z1,z2,z6,z4,z22]),(0,[z0,z1,z2,z6,z4,z441,z5]),(0,[z0,z84,z1,z64,z6,z4,z5]),(0,[z0,z387,z1,z2,z6,z4,z5])],[(1,[z0,z1,z2,z442,z4,z5])],[(0,[z443,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z4,z209,z5]),(0,[z0,z1,z2,z6,z444,z4,z5]),(0,[z0,z1,z2,z6,z445,z4,z5]),(0,[z0,z1,z2,z6,z4,z446,z5]),(0,[z0,z1,z2,z6,z447,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z448]),(0,[z0,z1,z2,z6,z449,z4,z5]),(0,[z0,z84,z1,z2,z177,z4,z5])]],
   [[(0,[z0,z1,z2,z330,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z450,z5]),(0,[z0,z198,z1,z2,z6,z4,z28]),(0,[z0,z1,z2,z6,z451,z4,z5]),(0,[z452,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z453,z4,z5]),(0,[z222,z0,z1,z2,z6,z4,z5]),(0,[z0,z454,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z455,z6,z4,z5])],[(0,[z0,z456,z1,z2,z6,z4,z5]),(0,[z457,z0,z1,z2,z6,z4,z5]),(0,[z0,z458,z1,z2,z6,z4,z5])],[(0,[z0,z1,z459,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z460]),(0,[z0,z1,z2,z6,z4,z121,z5])],[(0,[z0,z1,z2,z461,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z462,z5]),(0,[z0,z1,z2,z6,z463,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z175]),(0,[z0,z1,z2,z6,z177,z4,z5]),(0,[z464,z0,z1,z2,z6,z4,z5]),(0,[z0,z16,z1,z2,z6,z4,z139]),(0,[z465,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z2,z6,z4,z5]),(0,[z222,z1,z2,z6,z8,z4,z5]),(0,[z466,z0,z1,z2,z19,z4,z5]),(0,[z50,z0,z1,z2,z6,z68,z5]),(0,[z467,z0,z1,z2,z6,z4,z5]),(0,[z0,z468,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z469,z4,z5]),(0,[z0,z1,z2,z470,z6,z4,z5])],[(0,[z0,z20,z130,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z471]),(0,[z0,z1,z237,z2,z6,z4,z5]),(0,[z472,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z473,z4,z5]),(0,[z0,z474,z1,z2,z6,z4,z5]),(0,[z306,z0,z1,z2,z6,z4,z5]),(0,[z0,z316,z1,z2,z6,z4,z5]),(0,[z475,z0,z1,z2,z6,z4,z5])]],
   [[(0,[z61,z0,z1,z2,z261,z4,z5]),(0,[z52,z0,z130,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z4,z476,z5]),(0,[z0,z1,z2,z4,z321,z71,z5]),(0,[z0,z1,z2,z6,z105,z86,z5])],[(0,[z0,z477,z1,z2,z6,z4,z5]),(0,[z136,z0,z1,z2,z6,z4,z5]),(1,[z0,z1,z2,z8,z4,z5]),(1,[z0,z20,z2,z99,z4,z5]),(0,[z0,z182,z1,z2,z6,z4,z5])],[(0,[z274,z0,z1,z2,z19,z4,z5]),(0,[z0,z478,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z479,z6,z4,z5])],[(1,[z73,z1,z172,z6,z4,z5]),(0,[z0,z480,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z481,z5])],[(1,[z0,z257,z2,z6,z4,z5]),(0,[z0,z482,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z58,z68,z5]),(0,[z0,z483,z1,z2,z6,z4,z5]),(1,[z0,z1,z2,z6,z5,z149])],[(0,[z0,z1,z2,z6,z484,z4,z5]),(0,[z0,z15,z1,z64,z2,z4,z5])],[(1,[z0,z1,z17,z6,z4,z5]),(0,[z0,z1,z23,z6,z208,z4,z5])],[(0,[z485,z0,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z1,z2,z486,z6,z4,z5]),(1,[z0,z1,z64,z65,z4,z5])],[(0,[z487,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z19,z214,z4,z5]),(0,[z0,z488,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z489,z5])],[(0,[z61,z0,z280,z2,z6,z4,z5]),(1,[z0,z1,z2,z6,z4,z340]),(0,[z0,z1,z2,z6,z4,z5,z490]),(0,[z0,z1,z2,z6,z491,z4,z5]),(0,[z0,z1,z2,z6,z4,z492,z5])],[(0,[z0,z1,z2,z6,z4,z493,z5]),(0,[z0,z1,z2,z19,z6,z4,z5]),(0,[z0,z207,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z8,z105,z4,z5]),(0,[z494,z0,z1,z2,z6,z4,z5]),(0,[z0,z128,z2,z19,z6,z4,z5]),(1,[z0,z45,z227,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z495,z5])],[(0,[z0,z1,z2,z496,z6,z4,z5]),(0,[z0,z0,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z28]),(0,[z0,z1,z2,z6,z4,z5,z497]),(0,[z0,z1,z2,z6,z498,z4,z5]),(0,[z0,z1,z499,z2,z6,z4,z5])],[(0,[z0,z1,z2,z202,z6,z4,z5]),(0,[z500,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z59,z5]),(0,[z0,z501,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z502,z5]),(0,[z503,z0,z1,z2,z6,z4,z5])],[(0,[z0,z280,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z504,z19,z4,z5]),(0,[z0,z1,z2,z6,z68,z4,z5]),(0,[z0,z1,z2,z505,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z506,z5]),(0,[z0,z1,z2,z6,z507,z4,z5])],[(0,[z0,z1,z2,z6,z4,z5,z508]),(0,[z0,z1,z2,z8,z8,z4,z5]),(0,[z0,z1,z2,z6,z509,z4,z5]),(0,[z0,z1,z2,z6,z4,z510,z5])]],
   [[(0,[z0,z286,z1,z2,z6,z4,z5]),(0,[z0,z160,z2,z6,z4,z9,z5]),(0,[z274,z0,z1,z2,z235,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z511]),(0,[z0,z512,z1,z2,z6,z4,z5])],[(0,[z0,z513,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z178,z6,z4,z5]),(0,[z27,z0,z1,z2,z514,z4,z5]),(0,[z0,z1,z2,z515,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z516,z5])],[(0,[z73,z0,z1,z2,z336,z4,z5]),(0,[z0,z1,z517,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z4,z518,z5]),(0,[z0,z1,z2,z519,z6,z4,z5]),(0,[z0,z387,z1,z2,z6,z5,z79]),(0,[z0,z1,z2,z6,z4,z520,z5])],[(0,[z61,z52,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z521,z4,z5]),(0,[z522,z0,z1,z2,z6,z4,z5])],[(0,[z466,z0,z1,z2,z6,z4,z5]),(0,[z136,z0,z1,z178,z6,z4,z5])],[(0,[z0,z523,z2,z178,z6,z4,z5]),(0,[z0,z16,z1,z2,z8,z4,z5]),(0,[z524,z0,z1,z2,z6,z4,z5]),(0,[z525,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z526])]],
   [[(0,[z0,z527,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z528,z4,z5])],[(0,[z52,z0,z36,z2,z6,z4,z5]),(0,[z529,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z273,z4,z5]),(0,[z0,z1,z2,z6,z4,z476,z5]),(0,[z0,z1,z2,z6,z4,z185,z28]),(0,[z0,z1,z530,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z531,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z532])],[(0,[z0,z1,z2,z8,z4,z48,z5]),(0,[z274,z0,z1,z2,z6,z4,z185]),(0,[z0,z1,z2,z514,z6,z4,z5]),(0,[z0,z533,z1,z2,z6,z4,z5])],[(0,[z0,z47,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z139])],[(0,[z0,z1,z2,z6,z534,z4,z5]),(0,[z0,z1,z2,z227,z6,z4,z5]),(0,[z0,z1,z2,z535,z6,z4,z5])],[(0,[z0,z1,z2,z51,z19,z4,z5]),(0,[z0,z536,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z537,z4,z5]),(0,[z0,z92,z1,z2,z6,z58,z5]),(1,[z0,z70,z1,z2,z6,z4])]],
   [[(1,[z222,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z538,z5]),(0,[z0,z1,z64,z2,z177,z4,z5]),(0,[z0,z182,z1,z237,z2,z6,z4])],[(0,[z61,z0,z130,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z539,z5]),(0,[z73,z0,z1,z2,z19,z4,z5]),(0,[z0,z75,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z540,z4,z5])],[(0,[z274,z0,z1,z2,z442,z4,z5]),(0,[z0,z1,z2,z6,z541,z4,z5]),(0,[z0,z542,z1,z2,z6,z4,z5])],[(0,[z52,z0,z2,z6,z58,z4,z5]),(0,[z0,z1,z331,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z543,z5]),(0,[z544,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z545,z2,z6,z4,z5])],[(0,[z0,z1,z107,z2,z19,z4,z5]),(0,[z546,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z547,z6,z4,z5]),(1,[z0,z1,z2,z514,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z548])],[(0,[z0,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z549,z2,z8,z4,z5]),(0,[z0,z1,z2,z19,z239,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z185]),(0,[z0,z550,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z551,z5]),(0,[z0,z198,z82,z2,z6,z4,z5]),(0,[z552,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z553,z4,z5]),(0,[z0,z554,z1,z2,z6,z4,z5])],[(0,[z0,z40,z2,z6,z58,z4,z5])],[(0,[z0,z1,z2,z504,z6,z4,z5]),(0,[z0,z1,z555,z2,z6,z4,z5])]],
   [[(0,[z466,z0,z1,z2,z8,z4,z5]),(0,[z62,z1,z2,z19,z6,z4,z5]),(0,[z0,z92,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z195]),(0,[z0,z556,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z557,z6,z4,z5]),(0,[z62,z0,z1,z2,z19,z4,z5]),(0,[z0,z558,z1,z2,z6,z4,z5]),(0,[z559,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z560]),(0,[z0,z123,z1,z2,z6,z4,z5])],[(0,[z561,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z562,z5]),(0,[z0,z1,z2,z6,z4,z5,z563]),(0,[z0,z1,z2,z176,z177,z4,z5]),(0,[z0,z1,z564,z2,z6,z4,z5])],[(0,[z0,z1,z565,z2,z6,z4,z5]),(0,[z27,z0,z1,z2,z252,z4,z5]),(0,[z0,z1,z2,z6,z4,z566,z5])],[(0,[z0,z1,z2,z6,z4,z5,z567]),(1,[z0,z2,z6,z4,z353,z5])],[(0,[z274,z0,z1,z2,z8,z4,z5]),(0,[z0,z128,z1,z2,z19,z4,z5]),(0,[z0,z130,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z568,z5]),(0,[z0,z1,z569,z2,z6,z4,z5]),(0,[z0,z84,z1,z2,z232,z4,z5]),(0,[z0,z1,z6,z4,z209,z5,z79])],[(0,[z0,z1,z570,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z571,z5]),(0,[z572,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z237,z2,z6,z4,z79]),(0,[z0,z1,z2,z6,z573,z4,z5])],[(0,[z61,z0,z1,z2,z3,z4,z5]),(0,[z61,z0,z1,z2,z6,z7,z5]),(0,[z50,z43,z1,z2,z6,z4,z5]),(0,[z43,z0,z1,z2,z31,z4,z5]),(0,[z0,z574,z1,z2,z6,z4,z5])]],
   [[(1,[z0,z523,z2,z6,z4,z5]),(0,[z0,z575,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z576,z5]),(0,[z0,z1,z2,z177,z4,z48,z5])],[(0,[z52,z0,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z577]),(0,[z0,z578,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z579])],[(1,[z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z580,z4,z5]),(0,[z0,z1,z2,z6,z232,z4,z5]),(0,[z0,z581,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z336,z4,z5]),(0,[z0,z1,z2,z582,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z53,z5]),(0,[z0,z1,z2,z6,z4,z583,z5])],[(0,[z0,z1,z2,z6,z4,z5,z584]),(1,[z0,z128,z2,z19,z4,z5])],[(0,[z0,z585,z1,z2,z6,z4,z5]),(0,[z136,z73,z1,z2,z6,z4,z5]),(0,[z586,z0,z1,z2,z6,z4,z5]),(0,[z0,z587,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z245]),(0,[z0,z1,z2,z6,z4,z588,z5])],[(0,[z0,z1,z2,z180,z19,z4,z5]),(0,[z0,z1,z589,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z590,z4,z5])],[(0,[z0,z1,z2,z6,z4,z591,z5]),(0,[z0,z0,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z592]),(0,[z0,z1,z2,z593,z6,z4,z5])]],
   [[(0,[z0,z594,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z595,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z596,z5]),(0,[z0,z16,z1,z2,z6,z4,z48])],[(0,[z0,z280,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z145])],[(0,[z61,z0,z36,z2,z6,z4,z5]),(0,[z136,z0,z1,z2,z372,z4,z5]),(0,[z0,z1,z597,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z4,z86,z5]),(0,[z50,z1,z2,z6,z4,z9,z5]),(0,[z0,z1,z2,z6,z4,z5,z598]),(0,[z0,z1,z599,z2,z6,z4,z5]),(0,[z0,z1,z64,z2,z65,z4,z5])],[(0,[z0,z1,z2,z6,z4,z600,z5]),(0,[z0,z1,z2,z19,z4,z9,z5]),(0,[z0,z198,z1,z2,z19,z4,z5]),(0,[z0,z45,z1,z227,z6,z4,z5]),(0,[z601,z0,z1,z2,z6,z4,z5]),(0,[z0,z75,z182,z1,z2,z6,z5])],[(0,[z0,z602,z1,z2,z6,z4,z5]),(0,[z603,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z4,z5,z104]),(0,[z0,z1,z2,z604,z6,z4,z5]),(0,[z0,z2,z6,z120,z4,z9,z5]),(0,[z0,z207,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z605])],[(0,[z0,z1,z2,z6,z4,z7,z5]),(0,[z0,z1,z107,z2,z6,z4,z5]),(1,[z0,z1,z2,z252,z4,z5]),(0,[z0,z130,z1,z2,z99,z4,z5]),(0,[z0,z316,z1,z2,z4,z5,z79])],[(0,[z606,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z19,z4,z22,z5]),(0,[z0,z1,z2,z56,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z262,z5]),(0,[z0,z1,z607,z2,z6,z4,z5])],[(0,[z0,z608,z1,z2,z6,z4,z5]),(0,[z609,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z610,z4,z5]),(0,[z0,z1,z2,z6,z611,z4,z5]),(0,[z0,z198,z1,z2,z6,z4,z53]),(0,[z0,z612,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z1,z2,z6,z613,z4,z5]),(0,[z0,z1,z2,z6,z4,z353,z5])],[(1,[z0,z1,z2,z261,z4,z5]),(1,[z0,z1,z2,z233,z4,z5]),(0,[z0,z614,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z615,z5]),(0,[z0,z198,z2,z6,z4,z53,z5]),(0,[z0,z1,z2,z6,z4,z616,z5])],[(0,[z0,z1,z2,z24,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z617,z5]),(0,[z0,z1,z618,z2,z6,z4,z5]),(0,[z0,z619,z1,z2,z6,z4,z5]),(0,[z0,z1,z620,z2,z6,z4,z5]),(1,[z0,z103,z1,z2,z4,z5])],[(0,[z0,z1,z2,z621,z6,z4,z5])],[(0,[z61,z0,z1,z112,z6,z4,z5]),(0,[z0,z1,z523,z2,z6,z4,z5]),(0,[z0,z1,z2,z186,z6,z4,z5])],[(0,[z73,z1,z172,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z208,z4,z5]),(0,[z0,z1,z2,z622,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z623]),(0,[z0,z624,z1,z2,z6,z4,z5])],[(0,[z0,z1,z1,z2,z6,z4,z5]),(0,[z52,z0,z45,z2,z6,z4,z5]),(1,[z280,z1,z2,z8,z4,z5]),(0,[z0,z625,z1,z2,z6,z4,z5]),(0,[z0,z626,z1,z2,z6,z4,z5]),(0,[z0,z627,z1,z2,z6,z4,z5]),(0,[z0,z1,z237,z2,z6,z105,z4])],[(0,[z0,z47,z1,z2,z8,z4,z5]),(0,[z0,z628,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z1,z23,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z629,z5]),(0,[z0,z16,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z19,z4,z5,z79]),(0,[z0,z630,z1,z2,z6,z4,z5]),(1,[z0,z15,z1,z2,z210,z5]),(0,[z0,z1,z2,z6,z4,z5,z631]),(0,[z632,z0,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z19,z58,z4,z5]),(0,[z0,z1,z633,z2,z6,z4,z5]),(0,[z0,z1,z2,z235,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z634,z5]),(0,[z0,z635,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z636])],[(0,[z637,z0,z1,z2,z6,z4,z5]),(0,[z0,z638,z1,z2,z6,z4,z5]),(0,[z0,z130,z1,z2,z56,z4,z5]),(0,[z0,z92,z2,z6,z4,z59,z5])],[(0,[z0,z1,z2,z6,z4,z639,z5]),(0,[z73,z0,z1,z2,z8,z4,z5]),(0,[z0,z75,z1,z2,z8,z4,z5]),(0,[z0,z15,z1,z2,z19,z4,z5]),(0,[z0,z1,z237,z2,z6,z4,z209])],[(0,[z0,z1,z640,z2,z6,z4,z5]),(0,[z52,z0,z1,z2,z273,z4,z5]),(1,[z0,z1,z2,z202,z4,z5]),(0,[z0,z1,z2,z6,z4,z641,z5]),(0,[z43,z0,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z44,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z642])],[(0,[z643,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z604,z8,z4,z5]),(0,[z0,z644,z1,z2,z6,z4,z5]),(0,[z0,z645,z1,z2,z6,z4,z5])],[(0,[z61,z0,z1,z2,z6,z364,z5]),(0,[z0,z1,z107,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z436,z5]),(0,[z0,z1,z2,z19,z4,z210,z5]),(1,[z50,z1,z2,z6,z9,z5]),(0,[z0,z1,z2,z6,z646,z4,z5]),(0,[z0,z647,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z1,z2,z112,z6,z4,z5]),(0,[z0,z1,z172,z227,z6,z4,z5])],[(0,[z0,z1,z2,z6,z99,z4,z5]),(0,[z0,z648,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z649,z5]),(0,[z0,z1,z2,z91,z6,z4,z139])],[(0,[z0,z75,z1,z23,z6,z4,z5])],[(0,[z0,z650,z1,z2,z6,z4,z5]),(0,[z0,z92,z1,z2,z8,z4,z5])],[(0,[z0,z651,z1,z2,z6,z4,z5]),(0,[z62,z0,z1,z2,z8,z4,z5]),(0,[z0,z198,z1,z2,z6,z4,z5]),(0,[z0,z84,z1,z2,z65,z4,z5]),(0,[z652,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z209,z5])],[(0,[z653,z0,z1,z2,z6,z4,z5]),(0,[z654,z0,z1,z2,z6,z4,z5]),(1,[z0,z1,z2,z4,z321,z5]),(0,[z0,z1,z237,z6,z4,z209,z5]),(0,[z0,z655,z1,z2,z6,z4,z5])],[(0,[z0,z1,z549,z2,z6,z4,z5]),(1,[z0,z92,z2,z6,z59,z5]),(0,[z0,z1,z64,z2,z232,z4,z5]),(0,[z0,z47,z1,z6,z4,z5,z79]),(0,[z0,z1,z2,z6,z105,z4,z104]),(0,[z0,z1,z2,z6,z4,z5,z104])],[(0,[z0,z1,z656,z2,z6,z4,z5]),(0,[z0,z657,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z56,z6,z4,z5]),(0,[z0,z1,z2,z658,z6,z4,z5])]],
   [[(0,[z659,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z137,z6,z4,z5]),(0,[z0,z1,z660,z2,z6,z4,z5]),(0,[z0,z130,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z661]),(0,[z0,z75,z1,z2,z6,z86,z5])],[(0,[z662,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z663,z6,z4,z5]),(0,[z0,z1,z2,z4,z5,z145,z104])],[(0,[z0,z1,z2,z6,z664,z4,z5]),(0,[z0,z665,z1,z2,z6,z4,z5])],[(0,[z666,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z65,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z667,z5]),(0,[z0,z668,z1,z2,z6,z4,z5])],[(0,[z52,z0,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z4,z669,z5]),(0,[z0,z1,z2,z6,z4,z5,z670]),(0,[z0,z1,z2,z19,z4,z71,z5])],[(0,[z0,z1,z671,z2,z6,z4,z5]),(0,[z73,z0,z1,z172,z6,z4,z5]),(0,[z0,z672,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z263,z4,z5]),(0,[z0,z673,z1,z2,z6,z4,z5]),(0,[z0,z1,z674,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z675,z4,z5]),(0,[z0,z676,z1,z2,z6,z4,z5])],[(0,[z52,z0,z82,z2,z6,z4,z5]),(0,[z0,z1,z2,z622,z6,z4,z5]),(0,[z274,z0,z1,z2,z6,z4,z5]),(0,[z274,z1,z2,z6,z4,z5,z185]),(0,[z0,z1,z2,z6,z4,z677,z5])],[(0,[z0,z1,z2,z6,z4,z678,z5]),(0,[z0,z480,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z68,z59,z5]),(0,[z0,z1,z2,z6,z208,z4,z5])]],
   [[(0,[z52,z0,z92,z2,z6,z4,z5]),(0,[z0,z644,z1,z2,z8,z4,z5]),(1,[z62,z1,z2,z19,z4,z5])],[(0,[z0,z1,z2,z6,z679,z4,z5]),(0,[z0,z1,z2,z6,z442,z4,z5]),(0,[z0,z1,z680,z2,z6,z4,z5]),(0,[z0,z681,z1,z2,z6,z4,z5])],[],[(0,[z0,z1,z2,z19,z4,z440,z5]),(0,[z0,z40,z92,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z682,z4,z5]),(0,[z0,z82,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z31,z6,z4,z5]),(1,[z0,z207,z36,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z683]),(1,[z0,z82,z2,z6,z4,z28]),(0,[z0,z82,z1,z2,z6,z4,z28])],[(0,[z684,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z64,z2,z19,z4,z5]),(0,[z0,z1,z685,z2,z6,z4,z5]),(0,[z0,z686,z1,z2,z6,z4,z5]),(0,[z0,z15,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z687,z5])],[(0,[z0,z1,z2,z6,z364,z4,z5]),(0,[z0,z198,z1,z2,z8,z4,z5]),(0,[z0,z1,z688,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z689,z4,z5]),(0,[z0,z1,z2,z6,z4,z690,z5]),(0,[z0,z182,z1,z2,z6,z4,z86])],[(0,[z691,z0,z1,z2,z6,z4,z5]),(0,[z61,z0,z45,z2,z6,z4,z5]),(0,[z0,z692,z1,z2,z6,z4,z5]),(1,[z0,z130,z2,z56,z4,z5]),(0,[z0,z1,z2,z6,z4,z5,z693]),(0,[z0,z694,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z1,z2,z6,z4,z5,z5]),(0,[z0,z1,z2,z6,z105,z4,z5])],[(0,[z0,z1,z695,z2,z6,z4,z5]),(0,[z696,z0,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z56,z8,z4,z5])],[(0,[z0,z280,z1,z2,z6,z4,z5]),(0,[z0,z697,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z19,z177,z4,z5]),(0,[z0,z1,z2,z6,z698,z4,z5]),(1,[z0,z1,z6,z4,z5,z245])],[(1,[z0,z1,z2,z372,z4,z5]),(0,[z0,z1,z2,z8,z335,z4,z5]),(0,[z0,z1,z2,z663,z8,z4,z5]),(0,[z0,z699,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z700,z4,z5])],[(0,[z0,z1,z2,z6,z4,z701,z5]),(0,[z0,z1,z2,z6,z8,z4,z5])],[(0,[z0,z1,z2,z6,z4,z702,z5])],[(1,[z0,z1,z2,z6,z4,z241]),(0,[z0,z1,z703,z2,z6,z4,z5]),(0,[z0,z40,z1,z2,z6,z58,z5]),(0,[z0,z75,z1,z6,z4,z71,z5])],[(0,[z0,z1,z36,z172,z6,z4,z5]),(0,[z0,z1,z2,z176,z19,z4,z5]),(1,[z27,z1,z2,z6,z4,z22]),(0,[z0,z1,z2,z6,z4,z704,z5]),(0,[z0,z1,z2,z6,z4,z705,z5]),(1,[z0,z84,z1,z232,z4,z5]),(0,[z0,z1,z706,z2,z6,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z475,z1,z2,z19,z4,z5]),(0,[z0,z15,z1,z2,z210,z5])],[(0,[z0,z1,z2,z4,z707,z5])],[(0,[z0,z708,z1,z2,z6,z4]),(0,[z136,z257,z178,z6,z4,z5]),(0,[z0,z709,z1,z2,z4,z5]),(0,[z0,z1,z2,z6,z710,z5]),(0,[z0,z75,z70,z1,z6,z4]),(0,[z0,z16,z1,z2,z4,z299])],[(0,[z0,z160,z2,z6,z4,z5]),(0,[z0,z711,z2,z6,z4,z5]),(0,[z0,z1,z64,z4,z5,z226]),(0,[z0,z1,z2,z712,z4,z5]),(1,[z0,z47,z387,z1,z6]),(0,[z0,z1,z2,z713,z4,z5])],[(0,[z288,z1,z2,z8,z4,z5]),(0,[z714,z1,z2,z6,z4,z5])],[(0,[z0,z715,z2,z6,z4,z5]),(0,[z111,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z716,z4,z5]),(0,[z0,z1,z2,z4,z5,z175])],[(0,[z50,z1,z2,z6,z9,z5])],[(0,[z0,z1,z2,z186,z4,z5])]],
   [[(0,[z0,z1,z2,z717,z4,z5]),(0,[z0,z1,z2,z330,z177,z5]),(0,[z0,z1,z2,z4,z5,z718]),(0,[z0,z719,z1,z2,z4,z5]),(0,[z0,z1,z720,z6,z4,z5]),(0,[z0,z1,z2,z4,z721,z139]),(1,[z0,z1,z2,z6,z722])],[(0,[z61,z107,z2,z19,z4,z5]),(0,[z0,z723,z2,z6,z4,z5]),(0,[z0,z1,z2,z8,z105,z86]),(0,[z0,z128,z2,z56,z4,z5]),(0,[z0,z1,z2,z4,z121,z321])],[(0,[z0,z1,z2,z724,z4,z5]),(0,[z1,z2,z8,z240,z4,z5]),(0,[z274,z1,z2,z19,z4,z185]),(0,[z0,z316,z47,z1,z4,z79])],[(0,[z0,z1,z112,z8,z4,z5]),(0,[z0,z1,z2,z6,z725,z5]),(0,[z0,z1,z2,z726,z4,z5]),(0,[z407,z1,z2,z6,z9,z5]),(0,[z0,z1,z2,z4,z5,z727])],[(0,[z0,z1,z2,z201,z4,z5]),(0,[z0,z1,z2,z6,z728,z5]),(0,[z0,z1,z2,z729,z4,z5]),(0,[z407,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z730,z4,z5]),(0,[z0,z1,z2,z4,z321,z5])],[(0,[z0,z1,z2,z6,z731,z5]),(0,[z0,z1,z2,z732,z4,z5]),(0,[z52,z280,z2,z19,z4,z5]),(1,[z1,z2,z733,z4,z5]),(0,[z0,z734,z1,z8,z4,z5]),(0,[z0,z735,z1,z8,z4,z5]),(0,[z0,z123,z1,z8,z4,z5])],[(0,[z0,z40,z2,z8,z58,z5]),(0,[z0,z2,z19,z4,z353,z5]),(0,[z0,z1,z2,z736,z4,z5])],[(0,[z0,z2,z6,z58,z639,z5]),(0,[z0,z737,z1,z2,z4,z5]),(0,[z0,z738,z1,z2,z8,z4]),(0,[z62,z2,z19,z239,z4,z5]),(0,[z43,z1,z2,z19,z68,z5]),(0,[z0,z1,z2,z19,z4,z121]),(1,[z0,z2,z6,z4,z739])]],
   [[(0,[z0,z1,z740,z6,z4,z5]),(0,[z61,z565,z2,z6,z4,z5]),(0,[z136,z1,z741,z6,z4,z5]),(0,[z0,z1,z2,z176,z214,z5]),(1,[z0,z75,z70,z1,z6])],[(0,[z1,z2,z742,z8,z4,z5]),(0,[z0,z70,z1,z2,z8,z4]),(0,[z0,z1,z2,z8,z5,z743]),(0,[z0,z1,z64,z744,z4,z5]),(0,[z0,z123,z182,z1,z6,z104])],[],[(0,[z0,z1,z2,z261,z4,z340]),(0,[z0,z1,z2,z745,z4,z5]),(0,[z0,z182,z1,z6,z245,z104])],[(0,[z0,z1,z112,z6,z4,z340]),(0,[z0,z2,z6,z4,z53,z415]),(0,[z0,z746,z2,z6,z4,z5]),(0,[z0,z1,z2,z747,z4,z5])],[(0,[z61,z1,z2,z8,z4,z340]),(0,[z0,z1,z2,z4,z748,z5]),(0,[z0,z749,z2,z6,z4,z5]),(0,[z0,z160,z2,z8,z4,z5]),(0,[z0,z750,z2,z6,z4,z5]),(0,[z0,z1,z2,z4,z5,z721])],[(0,[z0,z1,z2,z8,z364,z5]),(0,[z0,z1,z2,z751,z4,z5]),(0,[z0,z128,z2,z8,z4,z5]),(0,[z0,z289,z2,z19,z4,z5]),(0,[z0,z692,z2,z6,z58,z5]),(0,[z0,z289,z2,z6,z4,z28]),(0,[z0,z182,z1,z2,z6,z532]),(0,[z0,z1,z2,z752,z4,z5])],[(0,[z0,z2,z6,z239,z4,z5]),(0,[z62,z1,z2,z19,z4,z5]),(0,[z1,z2,z57,z19,z4,z5]),(0,[z306,z1,z2,z19,z4,z5])]],
   [[(0,[z0,z1,z2,z6,z4,z753]),(0,[z280,z2,z24,z6,z4,z5]),(0,[z27,z1,z2,z514,z4,z22])],[(0,[z0,z1,z2,z754,z4,z5]),(0,[z0,z755,z2,z6,z4,z5]),(0,[z756,z1,z2,z6,z4,z5]),(0,[z0,z757,z1,z2,z4,z5])],[(0,[z1,z758,z2,z6,z4,z5]),(0,[z0,z759,z1,z2,z8,z5]),(0,[z0,z289,z2,z6,z4,z53]),(0,[z0,z1,z2,z760,z4,z5]),(0,[z0,z761,z2,z6,z4,z5]),(0,[z0,z1,z2,z762,z4,z5])],[(0,[z0,z1,z17,z6,z364,z5]),(0,[z1,z2,z8,z4,z287,z5]),(0,[z0,z82,z2,z6,z4,z28])],[(0,[z0,z257,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z763]),(0,[z0,z1,z2,z6,z764,z5]),(0,[z1,z2,z6,z4,z765,z185]),(0,[z1,z2,z766,z6,z4,z5])],[(0,[z0,z198,z2,z8,z4,z53]),(0,[z1,z2,z6,z767,z9,z5]),(0,[z274,z2,z6,z4,z353,z185]),(0,[z0,z2,z768,z6,z4,z5])],[(0,[z166,z1,z2,z8,z4,z5]),(0,[z18,z1,z2,z8,z4,z5]),(0,[z0,z130,z2,z56,z4,z5]),(0,[z769,z1,z2,z6,z4,z5])],[(0,[z0,z45,z768,z6,z4,z5]),(1,[z0,z1,z6,z4,z770]),(0,[z0,z15,z1,z2,z771,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z241]),(0,[z0,z772,z1,z2,z4,z5]),(0,[z0,z1,z2,z773,z4,z5])],[(0,[z0,z1,z2,z6,z774,z5]),(0,[z0,z1,z2,z775,z4,z5])],[(0,[z61,z107,z2,z6,z4,z5]),(0,[z0,z1,z776,z6,z4,z5]),(0,[z0,z777,z2,z6,z4,z5]),(0,[z0,z2,z19,z778,z4,z5]),(0,[z0,z779,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z780,z5]),(0,[z0,z781,z1,z2,z8,z4]),(0,[z0,z123,z182,z1,z6,z5])],[(0,[z0,z1,z2,z6,z4,z782]),(0,[z32,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z622,z4,z440]),(0,[z0,z75,z1,z6,z33,z5])],[(0,[z0,z67,z2,z24,z4,z5]),(0,[z0,z1,z2,z4,z48,z497]),(0,[z0,z1,z2,z4,z48,z721])],[(0,[z52,z280,z2,z6,z4,z5]),(0,[z0,z1,z2,z783,z4,z5]),(0,[z0,z47,z387,z1,z6,z5]),(0,[z0,z1,z6,z4,z5,z784])],[(0,[z0,z1,z2,z6,z7,z5]),(0,[z0,z258,z1,z335,z4,z5]),(0,[z0,z1,z2,z6,z785,z5]),(0,[z0,z1,z2,z786,z4,z5]),(0,[z0,z1,z2,z787,z4,z5])]],
   [[(0,[z0,z70,z1,z2,z19,z4]),(0,[z0,z47,z1,z19,z4,z79]),(0,[z0,z15,z1,z2,z489,z5]),(0,[z0,z788,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z105,z722])],[(0,[z61,z1,z2,z742,z4,z5]),(0,[z0,z1,z789,z6,z4,z5])],[(0,[z0,z2,z8,z4,z790,z5]),(0,[z274,z1,z2,z442,z4,z185])],[(0,[z0,z1,z2,z6,z791,z5]),(0,[z0,z1,z792,z6,z4,z5]),(0,[z43,z1,z2,z263,z68,z5]),(0,[z0,z2,z793,z99,z4,z5])],[(0,[z0,z1,z2,z31,z4,z5]),(0,[z0,z1,z2,z4,z5,z794])],[(0,[z0,z1,z2,z6,z795,z5]),(0,[z0,z1,z2,z6,z771,z5])],[(0,[z136,z523,z178,z6,z4,z5]),(0,[z50,z1,z2,z6,z767,z5])],[(0,[z1,z2,z733,z6,z4,z5]),(0,[z0,z796,z2,z19,z4,z5])]],
   [[(0,[z136,z1,z178,z6,z4,z5]),(0,[z1,z2,z741,z6,z4,z5])],[(0,[z0,z1,z2,z6,z5,z797]),(0,[z27,z1,z2,z252,z4,z22])],[(0,[z405,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z4,z5,z798]),(0,[z0,z1,z2,z91,z4,z440]),(0,[z799,z1,z2,z6,z4,z5]),(0,[z0,z75,z70,z1,z6,z71])],[(0,[z52,z2,z6,z276,z4,z5]),(0,[z0,z130,z2,z239,z4,z5]),(0,[z0,z800,z2,z6,z4,z5]),(0,[z0,z801,z2,z6,z4,z5])],[(0,[z0,z1,z2,z261,z4,z241]),(0,[z61,z107,z2,z8,z4,z5]),(0,[z559,z1,z2,z8,z4,z5]),(0,[z0,z2,z6,z4,z5,z802]),(0,[z0,z803,z1,z2,z6,z5]),(0,[z0,z182,z1,z2,z145,z104])],[(0,[z0,z1,z112,z6,z4,z241]),(0,[z274,z1,z2,z8,z4,z185]),(0,[z0,z1,z2,z6,z4,z739])],[(0,[z61,z1,z2,z8,z4,z241]),(0,[z0,z75,z1,z6,z121,z71])],[(0,[z0,z1,z2,z804,z4,z5]),(0,[z559,z1,z178,z6,z4,z5]),(0,[z0,z1,z744,z232,z4,z5]),(0,[z0,z1,z2,z91,z4,z48])]],
   [[(0,[z1,z2,z3,z8,z4,z5]),(0,[z52,z280,z2,z8,z4,z5]),(0,[z222,z1,z2,z733,z4,z5]),(0,[z1,z414,z2,z8,z4,z5]),(0,[z0,z1,z2,z805,z4,z5]),(0,[z0,z1,z2,z806,z4,z5])],[(0,[z0,z2,z8,z807,z4,z5]),(0,[z0,z808,z2,z6,z4,z5]),(0,[z43,z1,z2,z6,z767,z5]),(0,[z236,z1,z2,z6,z4,z185]),(1,[z0,z2,z793,z4,z5])],[(0,[z0,z2,z201,z239,z4,z5]),(0,[z43,z1,z2,z8,z68,z5]),(0,[z0,z1,z2,z8,z809,z4]),(0,[z0,z1,z2,z8,z4,z121]),(0,[z0,z1,z2,z4,z5,z810])],[(0,[z0,z1,z811,z6,z4,z5]),(0,[z0,z1,z2,z812,z4,z5]),(0,[z0,z1,z2,z330,z167,z5]),(0,[z0,z207,z768,z6,z4,z5]),(0,[z306,z2,z6,z99,z4,z5]),(0,[z0,z1,z813,z6,z4,z5])],[(0,[z0,z758,z2,z6,z4,z5]),(0,[z1,z2,z8,z528,z4,z5]),(0,[z0,z2,z8,z4,z5,z814])],[(0,[z61,z107,z2,z6,z4,z340]),(0,[z0,z1,z2,z815,z4,z5])],[(0,[z0,z734,z1,z6,z4,z5]),(0,[z0,z2,z6,z120,z4,z5]),(0,[z280,z758,z2,z6,z4,z5]),(0,[z0,z735,z1,z6,z4,z5]),(0,[z0,z123,z1,z6,z4,z5])],[(0,[z0,z1,z2,z4,z5,z816]),(0,[z0,z75,z70,z1,z2,z6])]],
   [[(0,[z61,z155,z2,z6,z4,z5]),(1,[z0,z768,z6,z4,z5])],[(0,[z0,z1,z817,z6,z4,z5]),(0,[z0,z289,z2,z8,z4,z5]),(0,[z1,z434,z2,z8,z4,z5]),(0,[z0,z75,z1,z19,z71,z5]),(0,[z0,z84,z1,z304,z4,z5])],[(0,[z0,z1,z2,z6,z7,z340]),(0,[z1,z2,z57,z8,z4,z5]),(0,[z306,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z663,z4,z48]),(0,[z0,z1,z2,z6,z5,z743]),(0,[z0,z818,z2,z6,z4,z5]),(0,[z0,z819,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z820]),(0,[z0,z1,z2,z6,z86,z560]),(0,[z0,z1,z23,z6,z5,z106]),(0,[z0,z1,z2,z4,z5,z145])],[(0,[z0,z821,z1,z2,z6,z5]),(0,[z0,z2,z8,z4,z353,z5]),(0,[z0,z1,z2,z771,z210,z5])],[(0,[z1,z2,z8,z4,z538,z5]),(0,[z0,z75,z1,z321,z71,z5])],[(0,[z0,z1,z2,z6,z822,z5]),(0,[z0,z1,z2,z823,z4,z5]),(1,[z0,z1,z2,z4,z721])],[(0,[z0,z1,z2,z6,z824,z5]),(0,[z0,z825,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z364,z5]),(0,[z0,z128,z2,z6,z4,z5]),(0,[z0,z257,z2,z8,z4,z5]),(0,[z212,z1,z2,z8,z4,z5]),(0,[z0,z1,z237,z19,z4,z209]),(0,[z0,z159,z1,z2,z262,z5]),(0,[z0,z1,z826,z6,z4,z5])]],
   [[(0,[z0,z316,z1,z2,z5,z149]),(0,[z0,z1,z2,z827,z4,z5]),(0,[z0,z1,z2,z176,z177,z5])],[(0,[z0,z828,z1,z2,z6,z5]),(0,[z0,z829,z2,z19,z4,z5]),(0,[z0,z1,z23,z19,z208,z5]),(0,[z0,z1,z2,z830,z4,z5])],[(0,[z550,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z831,z4,z5]),(0,[z0,z316,z387,z1,z2,z5]),(0,[z0,z1,z2,z6,z4,z721]),(0,[z0,z103,z123,z1,z4,z5]),(0,[z0,z1,z4,z5,z245,z145])],[(0,[z0,z1,z112,z261,z4,z5]),(0,[z0,z1,z2,z832,z4,z5])],[(0,[z0,z833,z2,z6,z4,z5]),(1,[z1,z741,z6,z4,z5]),(0,[z0,z1,z19,z4,z5,z245]),(0,[z0,z834,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z771,z5])],[(0,[z61,z1,z112,z8,z4,z5]),(0,[z0,z40,z2,z6,z835,z5])],[(0,[z0,z1,z2,z836,z4,z5]),(0,[z0,z258,z1,z232,z4,z5]),(0,[z0,z2,z6,z4,z837,z5]),(0,[z0,z2,z6,z835,z4,z5]),(0,[z0,z198,z2,z6,z4,z53]),(0,[z0,z103,z1,z4,z5,z245])],[(0,[z0,z838,z1,z2,z4,z5])]],
   [[(0,[z0,z839,z2,z6,z4,z5]),(0,[z73,z1,z172,z336,z4,z5]),(0,[z0,z1,z2,z840,z4,z5])],[(0,[z1,z741,z178,z6,z4,z5]),(0,[z0,z1,z2,z841,z4,z5])],[],[(0,[z0,z1,z842,z6,z4,z5]),(0,[z0,z47,z1,z8,z4,z79]),(0,[z0,z1,z8,z4,z5,z843]),(0,[z1,z2,z844,z6,z4,z5]),(0,[z0,z1,z2,z845,z4,z5])],[(0,[z483,z1,z2,z8,z4,z5]),(0,[z0,z160,z2,z6,z59,z5]),(0,[z0,z846,z2,z6,z4,z5])],[(0,[z0,z1,z64,z604,z4,z5])],[(0,[z61,z280,z2,z8,z4,z5]),(0,[z49,z280,z2,z8,z4,z5]),(0,[z0,z1,z8,z4,z847,z5]),(0,[z0,z644,z1,z2,z210,z5]),(0,[z0,z848,z2,z6,z4,z5]),(0,[z0,z849,z1,z2,z4,z5]),(0,[z0,z47,z387,z1,z6,z79]),(0,[z0,z16,z1,z2,z4,z721])],[(0,[z0,z130,z2,z3,z4,z5]),(0,[z0,z850,z2,z6,z4,z5]),(0,[z0,z15,z1,z2,z596,z5]),(0,[z0,z851,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z235,z4,z5]),(0,[z0,z1,z8,z852,z4,z5]),(0,[z0,z1,z2,z4,z5,z853])],[(0,[z0,z1,z2,z6,z4,z854]),(0,[z0,z1,z2,z855,z4,z5])],[(0,[z0,z47,z1,z4,z175,z79])],[(0,[z0,z1,z2,z856,z4,z5]),(0,[z1,z2,z19,z8,z4,z5]),(0,[z128,z2,z19,z8,z4,z5]),(0,[z50,z2,z6,z120,z9,z5]),(0,[z857,z1,z2,z6,z4,z5])],[(0,[z0,z858,z2,z6,z4,z5]),(0,[z0,z1,z2,z733,z4,z5])],[(0,[z0,z859,z1,z2,z4,z5]),(0,[z0,z15,z1,z2,z262,z5]),(0,[z130,z1,z2,z57,z4,z5]),(0,[z0,z2,z6,z4,z860,z5])],[(0,[z61,z107,z2,z6,z4,z241]),(0,[z0,z1,z2,z861,z4,z5]),(0,[z73,z1,z172,z19,z4,z5]),(0,[z0,z2,z19,z862,z4,z5]),(0,[z0,z863,z1,z6,z4,z5])],[(0,[z0,z1,z2,z864,z4,z5]),(0,[z0,z1,z2,z6,z4,z865]),(0,[z0,z1,z2,z19,z5,z149]),(0,[z1,z2,z6,z4,z765,z5]),(0,[z0,z1,z2,z866,z4,z5]),(0,[z0,z1,z2,z6,z4,z867]),(0,[z0,z1,z2,z793,z4,z5])]],
   [[(0,[z61,z107,z2,z3,z4,z5]),(0,[z52,z758,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z868]),(0,[z0,z1,z2,z4,z5,z869]),(0,[z0,z1,z2,z4,z5,z870])],[(0,[z0,z1,z17,z19,z4,z5]),(0,[z0,z1,z2,z8,z871,z5]),(0,[z0,z128,z2,z239,z4,z5]),(0,[z260,z1,z2,z19,z4,z5])],[(0,[z0,z1,z2,z872,z4,z5]),(0,[z0,z1,z2,z6,z364,z340]),(0,[z0,z829,z2,z6,z4,z5]),(0,[z1,z2,z6,z4,z22,z765]),(0,[z0,z873,z2,z6,z4,z5]),(0,[z0,z1,z23,z6,z208,z5]),(0,[z0,z1,z2,z4,z48,z631])],[(0,[z0,z1,z2,z6,z7,z241]),(0,[z1,z172,z741,z6,z4,z5]),(0,[z0,z513,z36,z6,z4,z5]),(0,[z0,z1,z2,z874,z4,z5]),(0,[z50,z160,z2,z6,z9,z5])],[(0,[z0,z1,z875,z6,z4,z5]),(0,[z61,z2,z8,z58,z4,z5]),(0,[z0,z1,z876,z6,z4,z5]),(0,[z0,z1,z2,z877,z4,z5]),(0,[z0,z1,z6,z208,z710,z5]),(0,[z0,z1,z6,z4,z770,z79]),(0,[z0,z1,z2,z878,z4,z5])],[(0,[z0,z1,z2,z879,z4,z5]),(0,[z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z19,z4,z340]),(0,[z0,z92,z2,z6,z835,z5])],[(0,[z0,z1,z2,z273,z4,z5]),(0,[z0,z1,z2,z880,z4,z5]),(0,[z0,z45,z227,z19,z4,z5]),(0,[z0,z2,z6,z4,z5,z881]),(0,[z0,z882,z1,z2,z4,z5]),(0,[z274,z1,z2,z6,z4,z185]),(0,[z0,z1,z768,z6,z4,z5]),(0,[z0,z16,z1,z2,z4,z139])],[(0,[z619,z1,z2,z19,z4,z5]),(0,[z50,z1,z2,z186,z9,z5]),(0,[z883,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z770])]],
   [[(0,[z0,z1,z2,z884,z4,z5])],[(0,[z0,z1,z2,z885,z4,z5]),(0,[z136,z1,z178,z372,z4,z5]),(0,[z0,z1,z2,z4,z5,z886])],[(0,[z52,z2,z6,z240,z4,z5]),(0,[z1,z2,z8,z4,z481,z5]),(0,[z0,z1,z2,z442,z4,z5]),(0,[z0,z119,z75,z1,z71,z5])],[(0,[z0,z1,z2,z887,z4,z5]),(0,[z0,z1,z2,z6,z809,z4]),(0,[z43,z1,z2,z6,z68,z5]),(0,[z0,z888,z1,z6,z4,z5]),(0,[z0,z1,z889,z6,z4,z5]),(0,[z0,z2,z6,z58,z835,z5]),(0,[z0,z1,z2,z6,z4,z121]),(0,[z0,z70,z1,z2,z4,z321]),(1,[z0,z1,z2,z771,z5])],[(0,[z52,z414,z2,z6,z4,z5]),(0,[z0,z75,z1,z8,z71,z5]),(0,[z0,z1,z2,z4,z890,z5]),(0,[z0,z891,z1,z6,z4,z5])],[(0,[z61,z130,z2,z8,z4,z5]),(0,[z0,z892,z1,z2,z4,z5]),(0,[z0,z1,z2,z176,z771,z5])],[(0,[z0,z92,z2,z19,z59,z5]),(0,[z893,z1,z2,z6,z4,z5]),(0,[z0,z894,z2,z6,z4,z5])],[(0,[z0,z1,z2,z895,z4,z5]),(0,[z0,z128,z2,z51,z4,z5]),(0,[z1,z2,z896,z6,z4,z5]),(0,[z0,z47,z1,z6,z149,z79])]],
   [[(0,[z0,z124,z1,z2,z4,z125]),(0,[z524,z1,z2,z8,z4,z5]),(0,[z0,z1,z6,z4,z847,z5]),(0,[z0,z1,z2,z6,z897,z5]),(0,[z0,z2,z56,z793,z4,z5]),(0,[z0,z1,z2,z6,z4,z898])],[(0,[z0,z1,z2,z4,z5,z899])],[(0,[z0,z289,z2,z6,z4,z5]),(0,[z0,z1,z2,z137,z4,z5]),(0,[z0,z1,z237,z8,z4,z209]),(0,[z0,z16,z1,z2,z4,z195]),(0,[z900,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z901,z4,z5]),(0,[z0,z182,z1,z2,z6,z394]),(0,[z0,z902,z2,z6,z4,z5])],[(0,[z306,z1,z2,z6,z4,z5]),(0,[z1,z2,z57,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z903]),(0,[z529,z1,z2,z8,z4,z5]),(0,[z0,z904,z1,z2,z6,z5]),(0,[z905,z1,z2,z6,z4,z5]),(0,[z906,z1,z2,z6,z4,z5])],[(0,[z61,z107,z2,z261,z4,z5]),(0,[z0,z1,z23,z8,z208,z5]),(0,[z503,z1,z2,z8,z4,z5])],[(0,[z61,z107,z112,z6,z4,z5]),(0,[z62,z128,z2,z19,z4,z5]),(0,[z0,z20,z2,z99,z4,z5]),(0,[z0,z2,z6,z4,z739,z28])],[(0,[z1,z2,z6,z4,z767,z5]),(0,[z0,z316,z1,z2,z4,z5]),(0,[z0,z1,z6,z208,z5,z563])],[(0,[z0,z1,z2,z6,z4,z907]),(0,[z0,z908,z2,z6,z4,z5])]],
   [[(0,[z0,z257,z2,z6,z4,z5]),(0,[z0,z1,z2,z909,z4,z5]),(0,[z0,z910,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z5,z149])],[(0,[z0,z1,z2,z261,z7,z5]),(0,[z0,z1,z2,z6,z911,z5]),(0,[z0,z1,z2,z4,z5,z912])],[(0,[z0,z1,z17,z6,z4,z5]),(0,[z0,z1,z112,z3,z4,z5]),(0,[z0,z1,z112,z6,z7,z5]),(0,[z0,z20,z2,z793,z4,z5]),(0,[z0,z1,z64,z4,z520,z5]),(0,[z0,z1,z2,z913,z4,z5])],[(0,[z61,z1,z2,z8,z7,z5]),(0,[z0,z914,z1,z2,z6,z4]),(0,[z0,z1,z2,z915,z4,z5])],[(0,[z0,z207,z36,z19,z4,z5]),(0,[z0,z916,z2,z19,z4,z5]),(0,[z1,z2,z6,z4,z5,z917]),(0,[z0,z1,z64,z65,z4,z5]),(0,[z0,z1,z6,z4,z209,z413])],[(0,[z26,z1,z2,z8,z4,z5])],[(0,[z0,z1,z918,z6,z4,z5]),(0,[z61,z758,z2,z6,z4,z5]),(0,[z423,z1,z2,z8,z4,z5]),(0,[z0,z821,z1,z2,z8,z5])],[(0,[z61,z628,z2,z6,z4,z5]),(0,[z0,z130,z2,z201,z4,z5]),(0,[z0,z1,z2,z336,z4,z5]),(0,[z0,z1,z2,z6,z919,z5]),(0,[z0,z920,z2,z6,z4,z5])]],
   [[(0,[z0,z708,z1,z2,z8,z4]),(0,[z0,z1,z2,z4,z921,z5])],[(0,[z922,z1,z2,z6,z4,z5]),(0,[z0,z16,z1,z2,z4,z592]),(0,[z0,z1,z2,z923,z4,z5])],[(0,[z0,z2,z6,z4,z924,z5]),(0,[z0,z47,z387,z1,z6,z4])],[(0,[z0,z1,z2,z6,z364,z241]),(0,[z0,z1,z2,z925,z4,z5])],[(0,[z0,z160,z2,z6,z7,z5]),(0,[z0,z1,z2,z926,z4,z5]),(0,[z0,z1,z2,z6,z927,z5]),(0,[z0,z75,z1,z6,z710,z5]),(0,[z0,z47,z1,z6,z4,z79])],[(0,[z0,z36,z112,z6,z4,z5]),(0,[z0,z128,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z364,z5]),(0,[z0,z2,z19,z239,z4,z5]),(0,[z0,z928,z1,z2,z4,z5])],[(0,[z0,z1,z2,z6,z4,z929]),(0,[z61,z36,z2,z8,z4,z5]),(0,[z930,z1,z2,z6,z4,z5]),(0,[z0,z123,z1,z6,z105,z4])],[(0,[z0,z1,z2,z6,z931,z5]),(0,[z0,z2,z6,z4,z790,z5]),(0,[z27,z1,z2,z19,z4,z22]),(0,[z0,z932,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z933,z6,z4,z5])],[(0,[z73,z1,z172,z8,z4,z5]),(0,[z0,z1,z2,z934,z4,z5]),(0,[z0,z1,z2,z935,z4,z5]),(0,[z0,z1,z2,z6,z936,z5]),(0,[z0,z1,z237,z6,z4,z510]),(0,[z937,z1,z2,z6,z4,z5])],[(0,[z0,z1,z2,z938,z4,z5]),(0,[z0,z1,z2,z8,z5,z149]),(0,[z1,z2,z8,z4,z690,z5])],[(0,[z0,z523,z2,z19,z4,z5]),(0,[z0,z796,z2,z6,z4,z5]),(0,[z1,z2,z8,z4,z5,z693]),(0,[z0,z939,z2,z8,z4,z5])],[(0,[z0,z1,z17,z8,z4,z5]),(0,[z694,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z177,z771,z5]),(0,[z0,z1,z2,z940,z4,z5])],[(0,[z0,z1,z2,z19,z4,z5]),(0,[z424,z1,z2,z19,z4,z5]),(0,[z0,z75,z1,z6,z394,z5]),(0,[z0,z1,z2,z941,z4,z5])],[(0,[z236,z1,z2,z8,z4,z5])],[(0,[z423,z1,z172,z6,z4,z5]),(0,[z0,z130,z2,z793,z4,z5])]],
   [[(0,[z0,z1,z2,z8,z4,z340]),(0,[z0,z942,z2,z6,z4,z5]),(1,[z1,z2,z6,z767,z5]),(0,[z0,z1,z2,z6,z722,z104])],[(0,[z0,z1,z2,z943,z4,z5]),(0,[z0,z45,z227,z8,z4,z5]),(0,[z0,z1,z944,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z945]),(0,[z0,z387,z1,z2,z6,z5])],[(0,[z0,z1,z2,z6,z871,z5]),(0,[z0,z946,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z5,z947])],[(0,[z0,z2,z6,z948,z4,z5]),(0,[z949,z1,z2,z6,z4,z5]),(0,[z0,z119,z70,z1,z2,z4])],[(0,[z222,z1,z2,z8,z4,z5]),(0,[z0,z1,z23,z6,z710,z5]),(0,[z0,z1,z2,z950,z4,z5])],[(0,[z0,z1,z17,z6,z4,z340]),(0,[z0,z1,z2,z951,z4,z5]),(0,[z0,z182,z1,z2,z6,z104])],[(0,[z0,z2,z6,z807,z4,z5]),(0,[z626,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z8,z952,z5]),(0,[z0,z1,z2,z180,z214,z5])],[(0,[z0,z1,z2,z4,z953,z5]),(0,[z0,z1,z6,z4,z5,z954]),(0,[z0,z1,z6,z744,z4,z5]),(0,[z0,z123,z1,z4,z5,z145])]],
   [[(0,[z0,z1,z2,z6,z4,z955]),(0,[z0,z1,z2,z956,z4,z5]),(0,[z0,z957,z1,z2,z4,z5]),(0,[z958,z1,z2,z6,z4,z5]),(0,[z0,z1,z959,z6,z4,z5])],[(0,[z0,z1,z2,z261,z364,z5]),(0,[z61,z2,z8,z285,z4,z5]),(0,[z0,z92,z2,z8,z59,z5]),(0,[z0,z2,z6,z4,z5,z814]),(0,[z0,z1,z331,z504,z4,z5]),(0,[z0,z768,z227,z6,z4,z5]),(0,[z0,z1,z2,z960,z4,z5]),(0,[z0,z1,z2,z961,z4,z5])],[(0,[z0,z1,z112,z6,z364,z5]),(0,[z0,z1,z962,z6,z4,z5]),(0,[z0,z1,z2,z963,z4,z5]),(0,[z0,z387,z1,z237,z2,z6])],[(0,[z61,z1,z2,z8,z364,z5]),(0,[z0,z1,z741,z6,z4,z5]),(0,[z0,z130,z2,z24,z4,z5]),(0,[z0,z1,z2,z964,z4,z5])],[(0,[z0,z759,z1,z2,z6,z5]),(0,[z0,z286,z1,z44,z4,z5])],[(0,[z0,z965,z1,z2,z4,z5]),(0,[z323,z1,z2,z8,z4,z5]),(0,[z0,z75,z1,z6,z71,z5])],[(0,[z0,z966,z2,z6,z4,z5])],[(0,[z1,z2,z496,z8,z4,z5]),(0,[z0,z1,z2,z967,z4,z5]),(0,[z522,z1,z2,z19,z4,z5]),(0,[z0,z2,z6,z835,z59,z5]),(0,[z0,z84,z1,z744,z4,z5]),(0,[z0,z968,z2,z6,z4,z5])]],
   [[(0,[z758,z107,z2,z6,z4,z5]),(0,[z0,z2,z6,z4,z353,z5]),(0,[z0,z1,z2,z4,z5,z969]),(0,[z27,z1,z2,z6,z4,z765])],[(0,[z0,z1,z2,z970,z4,z5])],[(0,[z0,z1,z2,z6,z971,z5])],[(0,[z61,z107,z2,z6,z7,z5]),(0,[z0,z1,z2,z972,z4,z5]),(0,[z0,z2,z973,z6,z4,z5]),(0,[z0,z1,z2,z974,z4,z5]),(0,[z306,z130,z2,z6,z4,z5]),(0,[z0,z975,z2,z6,z4,z5]),(0,[z0,z1,z237,z6,z4,z209])],[(0,[z0,z1,z2,z742,z4,z5]),(0,[z0,z523,z2,z6,z4,z5]),(0,[z52,z2,z6,z4,z538,z5])],[(0,[z0,z781,z1,z2,z6,z4]),(0,[z976,z1,z2,z6,z4,z5]),(0,[z1,z2,z6,z4,z5,z977])],[(0,[z0,z1,z2,z6,z4,z5]),(0,[z431,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z978,z4,z5]),(0,[z0,z75,z70,z1,z6,z5])],[(0,[z0,z1,z979,z6,z4,z5]),(0,[z0,z1,z2,z4,z980,z5]),(0,[z0,z124,z1,z2,z4,z139]),(0,[z981,z1,z2,z6,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z982]),(0,[z0,z983,z1,z2,z6,z5]),(0,[z0,z1,z2,z6,z984,z5]),(0,[z306,z130,z2,z56,z4,z5]),(0,[z0,z1,z2,z91,z4,z721])],[(0,[z0,z1,z2,z6,z4,z985]),(0,[z0,z1,z2,z263,z4,z5]),(0,[z0,z70,z1,z6,z208,z4])],[(0,[z0,z1,z2,z986,z4,z5]),(0,[z50,z1,z2,z19,z9,z5])],[(0,[z280,z1,z2,z273,z4,z5]),(0,[z0,z49,z2,z285,z4,z5]),(0,[z0,z946,z2,z6,z4,z5]),(1,[z1,z2,z6,z4,z765]),(0,[z0,z1,z6,z987,z4,z5])],[(0,[z0,z2,z19,z120,z4,z5]),(0,[z0,z988,z2,z6,z4,z5]),(0,[z0,z1,z2,z989,z4,z5]),(0,[z0,z1,z990,z6,z4,z5])],[],[(0,[z0,z289,z2,z6,z4,z241]),(0,[z0,z904,z1,z2,z8,z5]),(0,[z43,z1,z2,z31,z68,z5]),(0,[z0,z1,z991,z6,z4,z5])],[(0,[z0,z1,z2,z6,z992,z5]),(0,[z0,z36,z768,z6,z4,z5]),(1,[z0,z2,z6,z835,z5]),(0,[z0,z198,z2,z6,z4,z739]),(1,[z0,z1,z744,z4,z5]),(0,[z0,z1,z2,z6,z993,z5])]],
   [[(0,[z0,z1,z2,z6,z4,z994]),(0,[z0,z1,z2,z995,z4,z5]),(0,[z0,z1,z6,z4,z5,z843])],[(0,[z306,z1,z2,z3,z4,z5]),(0,[z62,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z6,z4,z996]),(0,[z130,z2,z56,z57,z4,z5]),(0,[z0,z1,z65,z744,z4,z5]),(0,[z0,z997,z2,z6,z4,z5])],[(0,[z0,z45,z112,z6,z4,z5]),(0,[z0,z1,z2,z998,z4,z5]),(0,[z27,z1,z2,z8,z4,z22]),(0,[z0,z999,z1,z2,z6,z4]),(0,[z0,z182,z1,z363,z2,z6])],[(0,[z0,z1,z2,z6,z4,z1000]),(0,[z0,z82,z2,z6,z4,z241]),(0,[z61,z2,z6,z285,z4,z5]),(0,[z61,z45,z2,z8,z4,z5]),(0,[z0,z1001,z2,z6,z4,z5])],[(0,[z0,z1002,z1,z2,z4,z5])],[(0,[z0,z1,z6,z852,z4,z5]),(0,[z0,z1,z2,z233,z4,z5]),(0,[z0,z1,z2,z1003,z4,z5])],[(0,[z0,z1,z17,z6,z4,z241]),(0,[z0,z523,z2,z8,z4,z5]),(0,[z0,z2,z6,z793,z4,z5]),(0,[z0,z70,z1,z23,z2,z6])],[(0,[z0,z1,z1004,z6,z4,z5]),(0,[z0,z75,z1,z77,z6,z5]),(0,[z0,z182,z1,z2,z6,z722])]],
   [[(0,[z0,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z1005,z4,z5]),(0,[z0,z1,z2,z1006,z4,z5]),(0,[z0,z47,z1,z6,z698,z4])],[(0,[z0,z1,z2,z1007,z4,z5]),(0,[z0,z2,z1008,z6,z4,z5]),(0,[z0,z750,z2,z19,z4,z5]),(0,[z0,z1,z2,z4,z5,z1009]),(0,[z0,z47,z1,z77,z6,z4])],[(0,[z280,z1,z2,z8,z4,z5]),(0,[z73,z1,z172,z6,z4,z5]),(0,[z0,z2,z8,z239,z4,z5]),(0,[z274,z1,z2,z6,z4,z765]),(1,[z0,z1,z6,z710,z5])],[(0,[z0,z1,z2,z1010,z4,z5]),(0,[z61,z2,z8,z4,z53,z5]),(0,[z0,z1,z2,z1011,z4,z5])],[(0,[z0,z939,z2,z6,z4,z5])],[(0,[z0,z2,z6,z58,z7,z5]),(0,[z0,z1012,z1,z2,z4,z5]),(0,[z0,z387,z1,z2,z5,z175]),(0,[z0,z1,z2,z1013,z4,z5])],[(0,[z0,z1,z2,z6,z4,z1014]),(0,[z0,z2,z19,z948,z4,z5]),(0,[z0,z1,z6,z4,z209,z770])],[(0,[z0,z82,z2,z19,z4,z28]),(0,[z0,z1015,z1,z2,z4,z5]),(0,[z0,z119,z1,z2,z4,z121]),(0,[z0,z47,z387,z1,z2,z6])]],
   [[(0,[z0,z1016,z1,z2,z4,z5]),(0,[z0,z480,z1,z2,z4,z195]),(0,[z0,z1,z2,z6,z4,z1017]),(0,[z0,z1,z2,z6,z5,z1018])],[(0,[z0,z1,z2,z6,z4,z340]),(0,[z0,z1,z2,z1019,z4,z5]),(0,[z0,z1,z2,z202,z4,z5]),(0,[z1,z2,z8,z225,z4,z5]),(0,[z0,z1,z2,z8,z4,z1020]),(0,[z0,z1,z331,z65,z4,z5]),(0,[z0,z1,z6,z4,z710,z5])],[(0,[z0,z1,z2,z6,z1021,z5]),(0,[z383,z1,z2,z19,z4,z5]),(0,[z0,z45,z227,z6,z4,z5]),(0,[z0,z1022,z2,z6,z4,z5]),(0,[z0,z1,z2,z4,z1023,z5]),(0,[z0,z123,z182,z1,z6,z4])],[(0,[z61,z107,z2,z6,z364,z5]),(0,[z61,z483,z2,z6,z4,z5]),(0,[z0,z82,z2,z6,z4,z739]),(0,[z0,z47,z1,z6,z4,z532])],[(0,[z0,z644,z1,z2,z436,z5]),(0,[z0,z1,z8,z4,z5,z245]),(0,[z1,z2,z229,z19,z4,z5])],[(0,[z0,z1,z2,z1024,z4,z5])],[(0,[z0,z777,z2,z19,z4,z5])],[(0,[z0,z1,z2,z6,z952,z5]),(1,[z128,z2,z8,z4,z5])]],
   [[(0,[z0,z2,z6,z4,z5,z1025]),(0,[z0,z1,z2,z8,z1026,z4]),(0,[z1,z2,z6,z68,z767,z5]),(0,[z0,z1,z2,z1027,z4,z5])],[(0,[z0,z1,z1028,z6,z4,z5]),(0,[z0,z1,z2,z1029,z4,z5]),(0,[z0,z1,z2,z19,z4,z241]),(0,[z2,z19,z8,z239,z4,z5]),(0,[z0,z1030,z1,z8,z4,z5])],[(0,[z0,z1,z2,z1031,z4,z5]),(0,[z0,z92,z2,z6,z59,z5])],[(0,[z0,z257,z112,z6,z4,z5]),(0,[z0,z1,z2,z19,z7,z5]),(0,[z61,z82,z2,z8,z4,z5]),(0,[z0,z1,z2,z1032,z4,z5]),(0,[z0,z1,z2,z1033,z4,z5])],[(0,[z0,z1,z17,z261,z4,z5]),(0,[z0,z387,z1,z2,z8,z5])],[(0,[z61,z92,z2,z8,z4,z5]),(0,[z0,z1034,z2,z6,z4,z5]),(0,[z0,z1,z2,z1035,z4,z5]),(0,[z0,z1,z2,z1036,z4,z5])],[(0,[z61,z1,z17,z8,z4,z5]),(0,[z0,z1,z2,z1037,z4,z5]),(0,[z0,z103,z182,z1,z2,z104])],[(0,[z0,z2,z6,z4,z53,z241]),(0,[z52,z280,z2,z201,z4,z5]),(0,[z0,z1,z2,z1038,z4,z5]),(0,[z73,z1,z741,z6,z4,z5]),(0,[z259,z1,z2,z8,z4,z5]),(0,[z0,z75,z47,z182,z1,z6])]],
   [[(0,[z0,z182,z1,z2,z8,z104]),(0,[z544,z1,z2,z19,z4,z5]),(0,[z0,z1,z1039,z6,z4,z5]),(0,[z0,z1040,z2,z6,z4,z5])],[(0,[z62,z128,z2,z6,z4,z5]),(0,[z0,z1,z2,z1041,z4,z5]),(0,[z0,z2,z6,z4,z739,z5])],[(0,[z50,z1,z2,z233,z9,z5]),(0,[z0,z1,z2,z4,z1042,z5]),(0,[z1043,z1,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z1044,z5]),(0,[z0,z47,z1,z6,z4,z770]),(0,[z0,z1,z6,z4,z5,z770]),(0,[z0,z387,z1,z6,z209,z5])],[(0,[z1,z2,z8,z276,z4,z5]),(0,[z0,z1,z2,z6,z4,z1045]),(0,[z0,z1,z237,z6,z4,z770])],[(0,[z0,z2,z201,z99,z4,z5]),(0,[z136,z1,z178,z19,z4,z5]),(0,[z0,z1,z2,z663,z4,z476]),(0,[z0,z738,z1,z2,z6,z4]),(0,[z122,z1,z2,z19,z4,z5]),(0,[z0,z1,z2,z1046,z4,z5]),(0,[z0,z1,z2,z1047,z4,z5]),(0,[z0,z2,z6,z1048,z4,z5]),(0,[z0,z1,z2,z6,z86,z722])],[(0,[z0,z1,z2,z1049,z4,z5]),(0,[z0,z257,z36,z6,z4,z5]),(0,[z73,z1,z172,z202,z4,z5]),(0,[z50,z1,z2,z8,z9,z5]),(0,[z274,z1,z2,z235,z4,z185]),(0,[z0,z1,z2,z6,z835,z5]),(0,[z0,z1050,z2,z6,z4,z5])],[(0,[z0,z70,z1,z2,z6,z4]),(0,[z0,z123,z1,z6,z86,z5])],[]],
   [[(0,[z0,z1,z2,z6,z4,z1051]),(0,[z652,z1,z2,z8,z4,z5]),(0,[z0,z916,z2,z6,z4,z5]),(0,[z0,z207,z36,z6,z4,z5])],[(0,[z61,z2,z8,z99,z4,z5]),(0,[z128,z1,z2,z8,z4,z5])],[(0,[z1,z2,z6,z4,z1052,z5]),(0,[z0,z1053,z1,z2,z4,z5]),(0,[z0,z1,z2,z1054,z4,z5])],[(0,[z0,z257,z227,z6,z4,z5]),(0,[z0,z1,z2,z514,z4,z5]),(0,[z295,z1,z2,z19,z4,z5]),(0,[z0,z20,z2,z239,z4,z5])],[(0,[z485,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z4,z1055,z5])],[],[(0,[z0,z1,z2,z6,z4,z1056]),(0,[z0,z1,z2,z19,z105,z86]),(0,[z0,z1,z6,z4,z5,z245])],[(0,[z0,z1,z2,z372,z4,z5]),(0,[z163,z1,z2,z8,z4,z5]),(0,[z0,z1,z2,z6,z767,z5]),(0,[z0,z2,z6,z4,z53,z739])]],
   [[(0,[z0,z1,z112,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z1057]),(0,[z0,z1,z1058,z6,z4,z5]),(0,[z0,z1,z2,z177,z5,z199])],[(0,[z0,z1,z2,z6,z1059,z5]),(0,[z0,z1,z2,z6,z4,z1060]),(0,[z0,z2,z8,z120,z4,z5]),(0,[z0,z160,z2,z6,z58,z5]),(0,[z0,z1,z2,z6,z4,z1061])],[(0,[z0,z1,z2,z6,z4,z241]),(0,[z0,z123,z1,z19,z4,z5]),(0,[z0,z1,z2,z6,z1062,z5])],[(0,[z0,z746,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z317]),(0,[z0,z40,z2,z19,z58,z5]),(0,[z0,z387,z1,z2,z19,z5]),(0,[z27,z1,z2,z6,z4,z22]),(0,[z0,z84,z1,z232,z4,z5]),(0,[z0,z1,z2,z1063,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z6,z4,z1064])],[(0,[z20,z1,z2,z57,z4,z5]),(0,[z18,z1,z2,z57,z4,z5]),(0,[z0,z1,z2,z1065,z4,z5])],[(0,[z0,z1,z2,z1066,z4,z5]),(0,[z52,z280,z2,z273,z4,z5]),(0,[z62,z1,z2,z733,z4,z5]),(0,[z0,z818,z2,z19,z4,z5]),(0,[z0,z819,z2,z19,z4,z5])],[(0,[z280,z2,z24,z8,z4,z5]),(0,[z0,z182,z1,z2,z19,z104]),(0,[z0,z1,z2,z4,z5,z1067])]],
   [[(0,[z0,z755,z2,z8,z4,z5]),(0,[z0,z1,z2,z1068,z4,z5]),(0,[z0,z1,z2,z6,z5,z722])],[],[(0,[z0,z207,z36,z8,z4,z5]),(0,[z0,z82,z2,z8,z4,z28]),(0,[z0,z160,z2,z19,z4,z5]),(0,[z0,z1069,z1,z2,z4,z5]),(0,[z0,z1,z2,z177,z677,z5]),(0,[z0,z1,z2,z1070,z4,z5])],[(0,[z61,z1,z2,z273,z4,z5]),(0,[z0,z1,z2,z19,z364,z5]),(0,[z0,z1,z2,z6,z1071,z5]),(0,[z0,z128,z2,z19,z4,z5]),(0,[z0,z49,z2,z99,z4,z5]),(0,[z0,z84,z1,z379,z4,z5])],[(0,[z0,z2,z6,z4,z1072,z5]),(0,[z1,z2,z334,z19,z4,z5]),(0,[z32,z1,z2,z6,z4,z22]),(0,[z0,z1,z2,z6,z1073,z5])],[(0,[z0,z1,z2,z6,z4,z1074]),(1,[z758,z2,z6,z4,z5]),(0,[z128,z2,z6,z8,z4,z5]),(0,[z0,z1075,z2,z6,z4,z5])],[(0,[z61,z648,z2,z6,z4,z5]),(0,[z0,z1,z2,z1076,z4,z5]),(0,[z0,z1,z1077,z6,z4,z5]),(0,[z0,z1078,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z1079])],[(0,[z274,z289,z2,z6,z4,z185])]],
   [[(0,[z0,z1,z2,z6,z4,z1080]),(0,[z0,z18,z2,z239,z4,z5]),(0,[z0,z2,z6,z862,z4,z5])],[],[(0,[z0,z1081,z2,z6,z4,z5]),(0,[z0,z1,z2,z6,z4,z1020]),(0,[z0,z198,z2,z19,z4,z53]),(0,[z0,z1,z1082,z6,z4,z5]),(0,[z0,z1,z2,z6,z105,z351]),(1,[z0,z123,z182,z1,z6])],[],[(0,[z0,z1,z2,z8,z4,z241]),(0,[z61,z223,z2,z6,z4,z5]),(0,[z0,z36,z313,z6,z4,z5]),(0,[z0,z1,z549,z604,z4,z5]),(0,[z0,z1,z2,z252,z4,z5]),(0,[z0,z1083,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1084]),(0,[z0,z1,z2,z6,z4,z1085]),(0,[z0,z1086,z2,z6,z4,z5])],[(0,[z0,z1,z2,z6,z1087,z5]),(0,[z0,z1,z2,z1088,z4,z5])],[(0,[z61,z107,z17,z6,z4,z5]),(0,[z0,z1,z2,z8,z7,z5]),(0,[z0,z1,z2,z1089,z4,z5])],[(0,[z61,z67,z2,z8,z4,z5]),(0,[z0,z2,z6,z778,z4,z5]),(0,[z0,z673,z2,z6,z4,z53]),(0,[z0,z1,z2,z744,z4,z5]),(0,[z0,z1,z2,z6,z105,z86])]],
   [[(0,[z0,z1,z2,z261,z4,z5]),(0,[z0,z1,z6,z4,z5,z1090]),(0,[z0,z1091,z1,z2,z4,z5])],[(0,[z0,z1,z112,z6,z4,z5]),(0,[z0,z1,z2,z6,z1026,z4]),(0,[z0,z1092,z1,z2,z6,z4]),(0,[z0,z1,z6,z710,z71,z5]),(0,[z0,z1,z2,z5,z149,z175]),(0,[z0,z103,z1,z2,z4,z5]),(0,[z0,z1,z2,z6,z4,z722])],[(0,[z61,z1,z2,z8,z4,z5]),(0,[z0,z92,z2,z6,z7,z5]),(0,[z0,z1,z2,z1093,z4,z5]),(0,[z1,z2,z256,z8,z4,z5]),(0,[z0,z1030,z1,z6,z4,z5]),(0,[z0,z848,z2,z19,z4,z5]),(0,[z0,z1,z2,z6,z4,z765]),(0,[z0,z119,z1,z2,z4,z5])],[(0,[z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z17,z6,z7,z5]),(0,[z1,z2,z375,z19,z4,z5]),(0,[z0,z128,z2,z99,z4,z5]),(0,[z0,z1,z2,z1094,z4,z5])],[(0,[z0,z2,z3,z99,z4,z5]),(0,[z136,z1,z178,z137,z4,z5]),(0,[z0,z40,z2,z6,z58,z5])],[(0,[z0,z2,z6,z4,z5,z1095]),(0,[z0,z1096,z1,z2,z4,z5])],[(0,[z1,z2,z733,z8,z4,z5]),(0,[z0,z84,z1,z44,z4,z5])],[(0,[z0,z1,z2,z3,z4,z340]),(0,[z0,z1,z2,z1097,z4,z5]),(0,[z136,z1,z178,z8,z4,z5]),(0,[z632,z1,z2,z8,z4,z5]),(0,[z1,z2,z19,z733,z4,z5]),(0,[z431,z1,z2,z6,z68,z5]),(0,[z0,z123,z182,z1,z2,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 536).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1072).take 88) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1160)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [536, 536, 88] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 119).take 137).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [119, 137] = true :=
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

end PEqualNP.Outside.L_meta_43166

theorem PEqualNP.Outside.L_meta_43166 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808362 * 2 ^ 32 + 4007714816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808362 * 2 ^ 32 + 4007714816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43166.solve