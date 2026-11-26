# Class sizes of elements of prime-power order in 17 finite simple groups

## Purpose

For each of the 17 finite simple groups $S$ listed in the code and each nonidentity element $s\in S$ of order $p^a$, with $p$ prime, we verify that

$$
|s^S|_{p'} \nmid |\operatorname{Mult}(S)|.
$$

Here $|s^S|_{p'}$ is the $p'$-part of the conjugacy class size of $s$. Class sizes are computed from CTblLib centralizer orders. The Schur multiplier orders come from the online *ATLAS of Finite Group Representations*. The source label `origin: ATLAS of finite groups` in the GAP output refers to the book *Atlas of Finite Groups* by Conway et al. (1985).

<details>
<summary>Multiplier orders and online ATLAS entries</summary>

| Group | GAP table | Multiplier order | Source |
| --- | --- | ---: | --- |
| $A_6$ | `A6` | 6 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/alt/A6/) |
| $A_7$ | `A7` | 6 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/alt/A7/) |
| $\mathrm{PSL}_3(4)$ | `L3(4)` | 48 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/lin/L34/) |
| $\mathrm{PSU}_4(3)$ | `U4(3)` | 36 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/U43/) |
| $\mathrm{P}\Omega^+_8(2)$ | `O8+(2)` | 4 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/O8p2/) |
| $\mathrm{PSU}_6(2)$ | `U6(2)` | 12 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/U62/) |
| $\mathrm{McL}$ | `McL` | 3 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/McL/) |
| $M_{22}$ | `M22` | 12 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M22/) |
| $\mathrm{P}\Omega_7(3)$ | `O7(3)` | 6 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/O73/) |
| $G_2(3)$ | `G2(3)` | 3 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/G23/) |
| $\mathrm{Suz}$ | `Suz` | 6 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/) |
| $\mathrm{Fi}_{22}$ | `Fi22` | 6 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/F22/) |
| ${}^2E_6(2)$ | `2E6(2)` | 12 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/TE62/) |
| $J_3$ | `J3` | 3 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J3/) |
| $\mathrm{Fi}_{24}'$ | `F3+` | 3 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/F24/) |
| $\mathrm{O'N}$ | `ON` | 3 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/ON/) |
| $\mathrm{Sz}(8)$ | `Sz(8)` | 4 | [ATLAS](https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/Sz8/) |

</details>

## GAP code

The computation used GAP 4.16dev and the GAP Character Table Library (CTblLib) 1.3.11.

```gap
# Each pair in rows gives a CTblLib table name and its Schur multiplier order.
if LoadPackage("ctbllib") = fail then
    Error("CTblLib is required");
fi;
SizeScreen([240, 100]);;

VerifyPrimePowerClasses := function()
    local rows, row, name, mu, tbl, n, orders, centralizers, i,
          primes, p, classSize, m, count, totalClasses, checkedClasses;
    rows := [
        ["A6", 6], ["A7", 6], ["L3(4)", 48], ["U4(3)", 36],
        ["O8+(2)", 4], ["U6(2)", 12], ["McL", 3], ["M22", 12],
        ["O7(3)", 6], ["G2(3)", 3], ["Suz", 6], ["Fi22", 6],
        ["2E6(2)", 12], ["J3", 3], ["F3+", 3], ["ON", 3],
        ["Sz(8)", 4]
    ];
    Print("VERSION GAP ", GAPInfo.Version, " CTBLLIB ",
          PackageInfo("ctbllib")[1].Version, "\n");
    totalClasses := 0;
    checkedClasses := 0;
    for row in rows do
        name := row[1]; mu := row[2];
        tbl := CharacterTable(name);
        if tbl = fail then Error("Missing character table: ", name); fi;
        n := Size(tbl);
        orders := OrdersClassRepresentatives(tbl);
        centralizers := SizesCentralizers(tbl);
        count := 0;
        for i in [1..Length(orders)] do
            if orders[i] > 1 then
                primes := Set(FactorsInt(orders[i]));
                if Length(primes) = 1 then
                    p := primes[1];
                    classSize := n / centralizers[i];
                    if not IsInt(classSize) then
                        Error("Nonintegral class size: ", name, " ", i);
                    fi;
                    m := classSize;
                    while m mod p = 0 do m := m / p; od;
                    if mu mod m = 0 then
                        Error("Nondivisibility failed: ", name, " class ", i);
                    fi;
                    count := count + 1;
                    Print("CHECK ", name, " class=", i, " element_order=",
                          orders[i], " p=", p, " class_size=", classSize,
                          " p_prime_part=", m, " multiplier_input=", mu, "\n");
                fi;
            fi;
        od;
        if count = 0 then Error("No prime-power classes checked: ", name); fi;
        totalClasses := totalClasses + Length(orders);
        checkedClasses := checkedClasses + count;
        Print("PASS ", name, " table=", Identifier(tbl),
              " all_classes=", Length(orders), " prime_power_classes=", count, "\n");
        Print("SOURCE ", Identifier(tbl), ": ", InfoText(tbl), "\n");
    od;
    Print("SUMMARY GROUPS ", Length(rows), " PASSED ", Length(rows),
          " ALL_CLASSES ", totalClasses, " PRIME_POWER_CLASSES ", checkedClasses,
          " FAILURES 0\n");
end;;

VerifyPrimePowerClasses();
QUIT;
```

## Summary

Of the 666 conjugacy classes in the 17 groups, 330 consist of nonidentity elements of prime-power order. In all 330 cases, the prime-to-$p$ part of the class size does not divide the Schur multiplier order. This verifies the finite cases in Lemma 5, step (3).

[Full GAP output](Output.md)
