
https://github.com/awalterschulze/regex-reexamined-coq

```
  𝒟ₐ L* = 𝒟ₐ (ϵ + L + L*L + L*L*L + ...)
       _ = 𝒟ₐ ϵ + 𝒟ₐ L + 𝒟ₐ L^2 + ... 𝒟ₐ L^n ...
```

  But

```
𝒟ₐ L^(n+1) = (𝒟ₐ L) * Lⁿ + ν L * (𝒟ₐ Lⁿ)
           = ∑₀∞ (𝒟ₐ L) * Lⁿ
```

```
  ∑₀∞ 𝒟ₐ L^(n+1) = ∑₀∞ ( (𝒟ₐ L) * Lⁿ  + ν L * (𝒟ₐ Lⁿ) )
                 = ∑₀∞ (𝒟ₐ L) * Lⁿ
```

  since νL*(𝒟ₐ L^(n-1))$ is either ∅ or it is 𝒟ₐ L^{n-1}, which is already included.
  Thus we have

```
  𝒟ₐ L∗ = ∑^∞ₙ₌₁ (𝒟ₐ L) * L^(n-1) 
      _ = (𝒟ₐ L) * ∑^∞ₙ₌₁ L^(n-1) 
      _ = (𝒟ₐ L) * L∗$,
```
