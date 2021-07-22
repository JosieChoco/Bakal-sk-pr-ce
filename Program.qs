namespace Shor {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Arithmetic;
    
    // ------------------------- Rabin-Millerův test prvočíselnosti -------------------------
    // Vstup: číslo N
    // Výstup: True = N je pravděpodobně prvočíslo, False = N je složené číslo
    // Opakuje Rabin-Millerův test k-krát
    operation isPrime(N : Int) : Bool {
        let k = 4;              // Počet provedených opakování, čím vyšší k, tím vyšší past úspěchu

        // Krajní případy
        if N <= 3 {
            return true;
        }
        if N <= 1 or N == 4 {
            return false;
        }

        // Pokud N je sudé, vrať false
        if (N % 2) == 0 {
            //Message("N je sudé...");
            return false;
        }

        mutable d = N - 1;
        if (d % 2) == 0 {
            repeat {
                set d = d / 2;
            } until (d % 2) != 0;
        }

        for i in 0 .. k {
            if RabinMillerTest(N, d) == false {
                return false;
            }
        }

        return true;
    }

    // Vstup: číslo N, číslo d
    // VýstupT: True = N je pravděpodobně prvočíslo, False = jinak
    operation RabinMillerTest(N : Int, d : Int) : Bool {
        //Message($"RabinMillerTest: N = {N}, d = {d}");
        mutable dV = d;
        // Vezmi random číslo a mezi 2 a N-2
        let max = N - 2;
        mutable a = 1;
        repeat {
            set a = RandomNumberInRange(max);
        } until a > 1;

        //Message($"RabinMillerTest: random číslo a = {a}");

        // Spočti a^d % n
        mutable x = ComputePowerMod(a, d, N);
        //mutable x = ComputePower(a, d) % N;

        //Message($"RabinMillerTest: a^d % N = {x}");

        if x == 1 or x == N - 1 {
            return true;
        }

        if dV != N - 1 {
            repeat {
                set x = (x * x) % N;
                set dV = dV * 2;
                //Message($"RabinMillerTest: x = {x}");
                //Message($"RabinMillerTest: dV = {dV}");

                if x == 1 {
                    return false;
                }
                if x == N - 1 {
                    return true;
                }
            } until dV == N - 1;
        }

        return false;
    }

    // Vstup: tři čísla
    // Výstup: x^y modulo p
    operation ComputePowerMod(x : Int, y : Int, p : Int) : Int {
        mutable result = 1;
        mutable xV = x % p;
        mutable yV = y;

        //Message($"ComputePowerMod: x = {x}, y = {y}, p = {p}");

        if x == 0 {
            return 0;
        }

        if yV > 0 {
            repeat {
                // Pokud je yV liché, přičti výsledek
                if (yV % 2) == 1 {
                    set result = (result * xV) % p;
                }
                set yV = yV / 2;
                set xV = (xV * xV) % p;
            } until yV < 1;
        }
        //Message($"ComputePowerMod: result = {result}");
        return result;
    }

    // -------------------------------------- Random Number Generátor --------------------------------
    operation GenerateRandomBit() : Result {
        // Alokace qubitu, vždy stav |0>
        use qubit = Qubit();
        // Dání qubitu do superpozice, tj. aplikování Hadamarda
        H(qubit);
        // Změření qubitu -> vrátí Zero nebo One
        return M(qubit);
    }

    operation RandomNumberInRange(max : Int) : Int {
        mutable output = 0;
        repeat {
            mutable bits = new Result[0];
            for indexBit in 1..BitSizeI(max) {      // generujeme náhodné bity, dokud nemáme požadovanou délku do max
                set bits += [GenerateRandomBit()];
            }
            set output = ResultArrayAsInt(bits);    // převede bitový string na pozitivní integer
        } until (output <= max);
        return output;
    }
    // -----------------------------------------------------------------------------------------------

    // --------------------------------- Spočti gcd(a, b) --------------------------------------------
    // Vstup: dvě čísla x a N
    // Výstup: nevětší společný dělitel čísel x a N
    operation ComputeGCD(x : Int, N : Int) : Int {
        mutable a = x;
        mutable b = N;

        if b == 0 {
            return a;
        } else {
            return ComputeGCD(b, a % b);
        }
    }

    // --------------------------------- Spočti n-tou mocninu čísla ----------------------------------
    // Vstup: dvě čísla x, n
    // Výstup: mocnina x^n
    operation ComputePower(x : Int, n : Int) : Int {
        if n == 0 {
            return 1;
        } elif n == 1 {
            return x;
        } elif n % 2 == 0 {
            let temp = ComputePower(x, n / 2);
            return temp * temp;
        } else {
            let temp = ComputePower(x, n / 2);
            return x * temp * temp;
        }
    }

    // --------------------------------- Najdi x a y tak, že N = x^y ---------------------------------
    // Vstup: číslo N
    // Výstup: číslo x tak, že N = x^y
    operation FindPower(N : Int) : Int {
        //Message("FindPower: Start");
        mutable count = SqrtInt(N);
        for x in 2..count {
            mutable y = 2;
            mutable power = 1;

            repeat {
                set power = ComputePower(x, y);
                if power == N {
                    return x;
                }
                set y = y + 1;
            } until power > N + 1;
        }
        // čísla x a y neexistují, vrať 0
        return 0;
    }

    operation SqrtInt(N : Int) : Int {
        if N == 0 or N == 1 {
            return N;
        }
        mutable i = 1;
        mutable result = 1;
        mutable end = false;
        repeat {
            if i*i == N {
                set end = true;
                set result = i;
            }
            if i*i > N {
                set end = true;
                set result = i - 1;
            }
            set i = i + 1;
        } until end == true;
        return result;
    }

    // --------------------------------- Shorův faktorizační algoritmus ------------------------------
    // Vstup: číslo N
    // Výstup: faktory čísla N, tj. pole Intů velikosti jedna nebo dvě
    operation ShorsAlgorithm(N : Int) : Int[] {
        mutable factors = new Int[0];
        mutable end = false;

        repeat {
            // 1) Vezmi náhodné číslo a v rozsahu 1..N
            mutable a = 1;
            repeat {
                set a = RandomNumberInRange(N);
            } until a > 1;

            //Message($"ShorsAlgorithm: Náhodné číslo a = {a}");

            // 2) Spočti gcd(a, N)
            mutable gcd = ComputeGCD(a, N);
            //Message($"ShorsAlgorithm: Společný dělitel gcd = {gcd}");
            // 3) Pokud gcd(a, N) != 1, pak máme netriviální faktor N a jsme hotovi
            if gcd != 1 {
                if gcd == N {
                    set factors += [gcd];
                    set factors += [1];
                    //Message($"ShorsAlgorithm: gcd(a, N) == N, tj faktory = {factors}");
                    return factors;
                } else {
                    set factors += [gcd];
                    set end = true;
                    //Message($"ShorsAlgorithm: gcd(a, N) != 1, tj faktor = gcd = {gcd}");
                    return factors;
                }
            } else {
                // 4) Jinak najdi periodu r, funkce f(x) = a^x mod N
                mutable r = 1;

                set r = FindPeriod(N, a);
                //Message($"ShorsAlgorithm: found period = {r}");

                // 5) Pokud je r liché, vrať se na krok 1)
                if r % 2 == 1 {
                    set end = false;
                    //Message($"ShorsAlgorithm: r je liché, r = {r}");
                } elif (ComputePower(a, r / 2) % N) == -1 {    // 6) Pokud a^(r/2) mod N = -1, vrať se na krok 1)
                    set end = false;
                    //Message($"ShorsAlgorithm: a^(r/2) mod N = -1, r = {r}");
                } else {
                    // 7) Jinak gcd(a^(r/2) + 1, N) a gcd(a^(r/2) - 1, N) jsou dva netriviální faktory N
                    let x = ComputePower(a, r / 2);
                    set factors += [ComputeGCD(x - 1, N)];
                    set factors += [ComputeGCD(x + 1, N)];
                    //Message($"ShorsAlgorithm: máme dva faktory = {factors}");
                    set end = true;
                    return factors;
                }
            }
        } until end == true;

        return factors;
    }

    // ------------------------------------ Kvantová část algoritmu -------------------------------------
    // Vstup: registr obsahující qubity pouze ve stavu |0>
    // Cíl: vytvoř superpozici pro každý stav, tj. aplikuj na každý qubit Hadamardovo hradlo
    operation HadamardTransformOnRegister(register : Qubit[]) : Unit is Adj + Ctl {
        ApplyToEachCA(H, register);
    }

    // Vstup: čísla N, a
    // Výstup: Najdi periodu r funkce a^x mod N
    operation FindPeriod(N : Int, a : Int) : Int {
        //Message($"FindPeriod: začínám hledat periodu pro N = {N}, a = {a}");
        mutable period = 1;
        // Potřebuju dva registry s velikostmi tak, že N^2 <= 2^size1
        let size1 = BitSizeI(N) * 2;
        let size2 = BitSizeI(N);

        repeat {
            use (register1, register2) = (Qubit[size1], Qubit[size2]);
            HadamardTransformOnRegister(register1);     // superpozice stavů registru 1
            // |register1> |register2 = 00..00> -> |register1> |a^register1 modulo N>
            ComputeQuantumExponent(N, a, register1, register2);
            //Message("FindPeriod: proběhlo spočítání exponentu");

            // Změř druhý registr a vyresetuj ho
            mutable resultTemp = new Result[size2];
            for i in 0..size2 - 1 {
                // Copy-and-update expressions
                //  original w/ itemAccess <- modification
                set resultTemp w/= i <- MResetZ(register2[i]);
            }

            // Aplikuj Kvantovou Fourierovu Transformaci na první registr
            QuantumFourierTransform(register1);

            //Message("FindPeriod: proběhla QFT na registru 2");

            // Změř první registr a vyresetuj ho
            mutable result = new Result[size1];
            for i in 0..size1 - 1 {
                set result w/= i <- MResetZ(register1[i]);
            }

            // Získej výsledek jako integer
            let resultBool = [false] + ResultArrayAsBoolArray(result);
            let resultBoolR = Reversed(resultBool);
            let resultBigInt = BoolArrayAsBigInt(resultBoolR);

            // Získej periodu - pozor, vše musí být datového typu BigInt
            mutable periodBigInt = 0L;
            let tempBigInt = 2L^size1;
            let gcdBigInt = GreatestCommonDivisorL(resultBigInt, tempBigInt);
            let numerator = resultBigInt / gcdBigInt;
            let denominator = tempBigInt / gcdBigInt;
            let NBigInt = IntAsBigInt(N);
            // function ContinuedFractionConvergentL (fraction : Microsoft.Quantum.Math.BigFraction, denominatorBound : BigInt) : Microsoft.Quantum.Math.BigFraction
            let appFraction = ContinuedFractionConvergentL(BigFraction(numerator, denominator), NBigInt);
            let (appNumerator, appDenominator) = appFraction!;

            if appDenominator < 0L {
                set periodBigInt = appDenominator * -1L;
            } else {
                set periodBigInt = appDenominator;
            }

            set period = ConvertBigIntToInt(periodBigInt);

            //Message($"FindPeriod: period candidate = {period}");

        } until (period != 0) and (ExpModI(a, period, N) == 1);

        //Message($"FindPeriod: found period = {period}");
        return period;
    }

    // Vstup: celá čísla N, a a dva kvantové registry |x>, |y>
    // Cíl: Spočti |x>|y> -> |x>|a^x mod N>
    operation ComputeQuantumExponent(N : Int, a : Int, register1 : Qubit[], register2 : Qubit[]) : Unit {
        //Message("ComputeQuantumExponent: start");
        let length1 = Length(register1);
        let length2 = Length(register2);
        X(register2[length2 - 1]);      // Aktuální stav: |y> = |00...01>

        for i in 0..length1 - 1 {
            mutable aMod = 1;
            for power in 1..ComputePower(2, (length1 - 1) - i) {
                set aMod = (aMod * a) % N;
            }
            //Controlled ComputeQuantumMultiplyModulus([register1[i]], (N, aMod, register2));
            Controlled MultiplyByModularInteger([register1[i]], (aMod, N, (LittleEndian(register2))));
        }
    }

    // Vstup: číslo n datového typu BigInt
    // Výstup: číslo n datového typu Int
    operation ConvertBigIntToInt(nBigInt : BigInt) : Int {
        Fact(BitSizeL(nBigInt) <= 64, $"ConvertBigIntToInt: nBigInt is too big");

        mutable nInt = 0;
        let array = BigIntAsBoolArray(nBigInt);
        let arrayReversed = Reversed(array);
        let length = Length(arrayReversed);

        for i in 0..length - 1 {
            if arrayReversed[i] and (length - 1) - i <= 31 {
                set nInt = nInt + 2^((length - 1) - i);
            }
        }

        return nInt;
    }

    // ------------------------------------
    // Vstup: celá čísla N, a a kvantový registr |y>
    // Cíl: spočítej |y> -> |ay mod N>
    // operation MultiplyByModularInteger (constMultiplier : Int, modulus : Int, multiplier : Microsoft.Quantum.Arithmetic.LittleEndian) : Unit is Adj + Ctl
    operation ComputeQuantumMultiplyModulus(N : Int, a : Int, register : Qubit[]) : Unit is Adj+Ctl {
        //Message("ComputeQuantumMultiplyModulus: start");
        let length = Length(register);
        let aMod = a % N;
        use x = Qubit[length];
        for i in 0..aMod - 1 {
            ComputeQuantumAddModulus(register, x, N);
        }
        // Aktuální stav: |y>|ay mod N>

        ApplyToEachCA(SWAP, Zipped(register, x));
        // Aktuální stav: |ay mod N>|y>

        let aInversed = InverseModI(aMod, N);
        for i in 0..aInversed - 1 {         // resetujeme každý qubit registru x
            Adjoint ComputeQuantumAddModulus(register, x, N);
        }
    }

    // Vstup:
    // Cíl: spočítej |x>|y> -> |x + y mod 2^n>, kde n je délka registru x i y
    operation ComputeQuantumAdd(register1 : Qubit[], register2 : Qubit[]) : Unit is Adj+Ctl {
        //Message("ComputeQuantumAdd: start");
        let length = Length(register1);
        QuantumFourierTransform(register2);
        for i in 0..length - 1 {
            for j in 0..length - 1 - i {
                Controlled R1Frac([register1[i+j]], (2, j+1, (register2)[(length - 1) - i]));
            }
        }

        Adjoint QuantumFourierTransform(register2); // QFT^-1
    }

    // Vstup: kvantový registr, celé číslo N
    // Cíl: spočítej |x> -> |x + a mod 2^n>, kde a je nějaké číslo
    operation ComputeQuantumAddNum(register : Qubit[], a : Int) : Unit is Adj+Ctl {
        //Message("ComputeQuantumAddNum: start");
        let length = Length(register);
        QuantumFourierTransform(register);
        for i in 0..length - 1 {
            for j in 0..length - 1 - i {
                if not(a / 2^((length - 1) - (i + j)) % 2 == 0) {
                    R1Frac(2, j + 1, (register)[length - 1 - i]);
                }
            }
        }
        
        Adjoint QuantumFourierTransform(register);  // QFT^-1
    }

    // Vstup: dva kvantové registry |x> a |y>, celé číslo N
    // Cíl: spočítat |x>|y> -> |x>|x + y mod N>
    operation ComputeQuantumAddModulus(register1 : Qubit[], register2 : Qubit[], N : Int) : Unit is Adj+Ctl {
        //Message("ComputeQuantumAddModulus: start");
        use (qubit1, qubit2) = (Qubit(), Qubit());
        use target = Qubit();
        // Oba registry zvětším o jeden qubit |0>, kvůli možnému přetečení
        let register1L = [qubit1] + register1;
        let register2L = [qubit2] + register2;
        ComputeQuantumAdd(register1L, register2L);
        // Aktuální stav registru: |x> |y> -> |x> |x + y>
        Adjoint ComputeQuantumAddNum(register2L, N);
        // Aktuální stav registru: |y> -> |y - N>
        Controlled X([register2L[0]], target);
        Controlled ComputeQuantumAddNum([target], (register2L, N));
        Adjoint ComputeQuantumAdd(register1L, register2L);  // |x>|y> -> |x>|y - x>
        X(target);
        Controlled X([register2L[0]], target);
        ComputeQuantumAdd(register1L, register2L);
    }

    // ------------------------------------------ Kvantová Fourierova Transformace ---------------------

    // Vstup: jeden qubit, k >= 0
    // Cíl: zrotovat qubit o e^(2i*pí / 2^i) kolem stavu |1> -> předdefinovaná operace R1Frac(Int, Int, Qubit)
    operation RotationTransform(qubit : Qubit, k : Int) : Unit is Adj+Ctl {
        R1Frac(2, k, qubit);
    }

    // Vstup: kvantový registr
    // Cíl: SWAP brána, která provede operaci registru |xyz> -> |zyx>
    // použitím předdefinované operace SWAP, která prohazuje dva qubity, vždy prohodím první s posledním, druhý s předposledním, ...atd
    operation SwapTransform(register : Qubit[]) : Unit is Adj+Ctl {
        let length = Length(register);
        for i in 0..length/2 - 1 {
            SWAP(register[i], register[length - 1 - i]);
        }
    }

    // Vstup:
    // Cíl: změnit stav regisru na 1/sgrt(2) * (|0> + e^(2i*pí*0.x1..xn))|1> XOR (x1..xn)
    // kde 0.x1..xn je binární zlomek odpovídající stavům registru |x1..xn>
    operation BinExponentPlace(register : Qubit[]) : Unit is Adj+Ctl {
        H(register[0]);
        let length = Length(register);
        for i in 1..Length(register) - 1 {
            Controlled RotationTransform([register[i]], (register[0], i + 1));
        }
    }

    // Vstup: Kvantový registr s n stavy |x1..xn>
    // Cíl: provézt změnu registru do stavu 1/sqrt(2) * Sum (e^(2i*pí*xk/2^n)|k>)
    operation QuantumFourierTransform(register : Qubit[]) : Unit is Adj+Ctl {
        let length = Length(register);
        for i in 0..length - 1 {
            BinExponentPlace(register[i ...]);
        }
        SwapTransform(register);
    }

    // ------------------------------------------ Faktorizace čísla N ----------------------------------
    // Vstup: číslo N
    // Výstup: faktorizace čísla N
    operation Factoring(N : Int) : Int[] {
        mutable factors = new Int[0];

        // Pokud je N = 0 nebo N = 1, vrať N a skonči
        if N == 0 or N == 1 {
            set factors += [N];
            //Message($"Factoring: N = 0 nebo N = 1, faktory = {factors}");
            return factors;
        }

        // Pokud je N prvočíslo, vrať faktory 1 a N, skonči
        if isPrime(N) == true {
            set factors += [1];
            set factors += [N];
            //Message($"Factoring: N je prvočíslo, faktory = {factors}");
            return factors;
        }

        // Pokud N = x^y, pro x,y >= 2, pak x je faktorem N
        let x = FindPower(N);
        if x != 0 {
            mutable count = 1;
            repeat {
                set factors += [x];
                set count = count * x;
            } until count == N;
            //Message($"Factoring: N = x^y, faktory = {factors}");
            return factors;
        }

        // Jinak hledej faktory tak dlouho, dokud nerozložíš N na součin faktorů
        mutable number = N;
        repeat {
            let power = FindPower(number);
            // Pokud je N sudé, faktor je 2
            if number % 2 == 0 {
                set factors += [2];
                set number = number / 2;
            } elif power != 0 {
                mutable c = 1;
                repeat {
                    set factors += [power];
                    set c = c * power;
                } until c == number;
                set number = number / c;
            } else {
                // Jinak najdi faktory Shorovým algoritmem
                let results = ShorsAlgorithm(number);
                let lengthResults = Length(results);
                for i in 0..lengthResults - 1 {
                    //set factors += [results[i]];
                    //set number = number / results[i];
                    // Pokud je některý z faktorů složené číslo, najdi jeho faktory
                    let checkPrime = isPrime(results[i]);
                    if checkPrime == false {
                        //Message($"Factoring: faktor {results[i]} není prvočíslo");
                        // Pokud factor[i] = x^y, pro x,y >= 2, pak x je faktorem factor[i]
                        let z = FindPower(results[i]);
                        if z != 0 {
                            mutable count = 1;
                            repeat {
                                set factors += [z];
                                set count = count * x;
                            } until count == results[i];
                            //Message($"Factoring: factor {results[i]} = x^y");
                        } else {
                            let resultsTemp = ShorsAlgorithm(results[i]);
                            let lengthResultsTemp = Length(resultsTemp);
                            for k in 0..lengthResultsTemp - 1 {
                                set factors += [resultsTemp[k]];
                            }
                        }
                        //let resultsTemp = ShorsAlgorithm(results[i]);
                        //let lengthResultsTemp = Length(resultsTemp);
                        //for k in 0..lengthResultsTemp {
                        //    set factors += [resultsTemp[k]];
                        //}
                        set number = number / results[i];
                    } else {
                        //Message($"Factoring: faktor {results[i]} jsou již prvočísla");
                        set factors += [results[i]];
                        set number = number / results[i];
                    }
                }
            }
        } until number == 1;

        //if N % 2 == 0 {
        //    set factors += [2];
        //    Message($"Factoring: N % 2 == 0, faktory = {factors}");
        //} else {
        //    let results = ShorsAlgorithm(N);
        //    let lengthResults = Length(results);
        //    for i in 0..lengthResults - 1 {
        //        set factors += [results[i]];
        //    }
        //    Message($"Factoring: Volám shorův algoritmus, faktory = {factors}");
        //}

        return factors;
    }

    // -------------------------------------- Hlavní operace Start ---------------------------------------
    @EntryPoint()
    operation Start(N : Int) : Int[] {
        Message("This is Shor's factoring algorithm for given N ... ");
        // return FindPeriod(21, 4);          // Změnit návratový typ na Int
        // FindPeriod(N, a),
        //      Pro N = 15, a = 11 -> r = 2
        //      Pro N = 15, a = 7 -> r = 4
        //      pro N = 11, a = 5 -> r = 5
        //      Pro N = 15, a = 14 -> r = 2
        //      Pro N = 21, a = 4 -> r = 3

        // Testovací vstupy, vypíše tabulku pro N = 1,.., 34
        for i in 1..9 {
            let factors = Factoring(i);
            Message($"N = {i},   factors = {factors}");
        }
        for i in 10..20 {
            let factors = Factoring(i);
            Message($"N = {i},  factors = {factors}");
        }
        for i in 21..32 {
            let factors = Factoring(i);
            Message($"N = {i},  factors = {factors}");
        }

        Message($"given number N = {N}, found factors:");
        return Factoring(N);
    }

    // Spuštění: dotnet run -N 28
}
