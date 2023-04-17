# Proof of Solvency in a CEX

Source: https://vitalik.ca/general/2022/11/19/proof_of_solvency.html

## Proof of liability
For simpliciy, we'll only consider ETH for now. So, CEX wants to prove that it has $a$ amount of ETH as liability. That means users have custodied $a$ ETH with the CEX.

List of all users along with their eth balance with the CEX:
$$
U = [(u_0, a_0),(u_1,a_1),...,(u_{2^l-1},a_{2^l-1})]
$$

This list includes all the users. All $a_i\geq0$ and $a=\Sigma_{i=0}^{i={2^l-1}}a_i$.

### Prepare KZG commitment
1. Create a vector from $U$:
   $$
   V = [hash(u_0,salt_0),a_0,...,hash(u_{2^l-1}, salt_{2^l-1}),a_{2^l-1}]
   $$
   Note that the length now is $2^l+1$.
2. Create $P(x)$ as the langrange polynomial to commit: $P(\omega^i) = V_i$. $comm(P)$ is the KZG commitment.
3. To each user u_i, send the opening proof of $V_{2i},V_{2i+1}$ (user hash and balance).

### Prove facts about balances
We need to prove that all $a_i$ committed in $P$ are non-negative and sum to $a$.

This can be done via a SNARK:

Define another polynomial $I(x)$. We have to constraint $I(x)$ via equations in such a way that these facts can be proven in a SNARK.

Some assumptions:
1. The maximum user balance is under $2^{k-1}$ (so fits in $k-1$ bits).
2. The total number of users is $2^l$.
3. $z$ is is an order $2^l\cdot k$-th root of unity (reason will be clear eventually).

Consider the sequence of tuples:
$(I(z^0),I(z^1),I(z^2),...,I(z^{k-1})),(I(z^{k}),...,I(z^{2k-1})),...$

Every $i_{th}$ element in this sequence (the $I$'s in brackets) correspond to $P(\omega^i)$ in a way we're going to define now:

Consider any tuple $[I(z^{ik}),...,I(z^{(i+1)k-1})]$. In this:
1. The first element is always $0$.
2. The subsequent elements are expanded by a bit($0$ or $1$) from the previous element except the last element.
3. The second to last element is equal to the $a_i$.

This ensures that $a_i$ is under $2^k$ because it cannot exceed $k$ bits.

The constraint on the last element in each tuple ensures that the sum of all user balances is $a$. The last element of the $i_{th}$ tuple stores the
$$
sum\ of\ first\ (i+1)\ user\ balances - ((i+1)*(average\ user\ balance))
$$

The last element of the last tuple has to be $0$ if the sum of all user balances is $a$.

1. Derive the average user balance $\overline{a}$: $\frac{a}{2^l}$.
2. Define $I(z^{k-1})$, the last element of the $0_{th}$ tuple as $a_0-\overline{a}$:
3. Define $I(z^{(i+1)k-1})$, last element of $i>0$ tuple as:
   $$
    a_i+ (last\ element\ of\ the\ previous\ sequence)-\overline{a}
   $$

With this, our equations become:
$$
I(z^{ik})=0\\
I(z^i) - 2I(z^{i-1}) \in \{0,1\};\ if\ i\ mod\ {k}\notin\{0,k-1\}\\
I(z^{(i+1)k-2}) = P(\omega^{2i+1})\\
I(z^{k-1}) = I(z^{k-2}) - \overline{a}\\
I(z^{(i+1)k-1}) = I(z^{(i+1)k-2}) + I(z^{ik-1}) - \overline{a};\ if\ i\neq 0\\
I(z^{2^lk-1}) = 0
$$

With these equations, we can create a SNARK out of it in Halo2.