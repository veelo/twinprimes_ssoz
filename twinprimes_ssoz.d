/**
 * Find the Twin Primes <= N using the Segmented Sieve of Zakiya (SSoZ)
 * This is a D port of the Nim program twinprimes_ssoz.nim:
 * https://gist.github.com/jzakiya/6c7e1868bd749a6b1add62e3e3b2341e
 *
 * This D source file, and subsequent modifications, can be found here:
 * https://gist.github.com/jzakiya/ae93bfa03dbc8b25ccc7f97ff8ad0f61
 *
 * To compile with ldc2: $ ldc2 --release -O3 twinprimes_ssoz.d
 *
 * Then run executable: $ ./twinprimes_ssoz <cr>, and enter value for N.
 * Or alternatively: $ echo <number> | ./twinprimes_ssoz
 * As coded, input values cover the range: 13 -- 2^64 - 1
 *
 * Related code, papers, and tutorials, are available here:
 * https://www.scribd.com/doc/228155369/The-Segmented-Sieve-of-Zakiya-SSoZ
 * https://mega.nz/#!yJxUEQgK!MY9dwjiWheE8tACtEeS0szduIvdBjiyTn4O6mMD_aZw
 * https://www.scribd.com/document/266461408/Primes-Utils-Handbook
 *
 * Originally coded by Vijay Nayar, modifed by Jabari Zakiya and
 * Bastiaan Veelo.
 * Version Date: 2018/11/8
 */
module twinprimes_ssoz;

import std.algorithm : maxElement, min, sort, swap;
import std.array : array;
import std.typecons : Rebindable;
import std.conv : to;
import std.datetime.stopwatch : StopWatch;
import std.math;
import std.numeric : gcd;
import std.parallelism : parallel, totalCPUs;
import std.range : iota;
import std.stdio : readf, write, writeln;

/// Compute modular inverse a^-1 of a to base b, e.g. a*(a^-1) mod b = 1.
int modInv(int a0, int b0) pure
{
  int a = a0;
  int b = b0;
  int x0 = 0;
  int result = 1;
  if (b == 1) {return result;}
  while (a > 1) {
    immutable q = a / b;
    a = a % b;
    swap(a, b);
    result -= q * x0;
    swap(x0, result);
  }
  if (result < 0) {result += b0;}
  return result;
}

/// Prime Generator Parameters
struct PgParameters {
  uint modulus;
  size_t residueCount;
  size_t twinPairsCount;
  uint[] residues;
  uint[] residueTwinPairs;
  uint[] residueInverses;
}

/// Creates constant parameters for given PrimeGenerator at compile time.
PgParameters genPgParameters(int prime) pure
{
  //pragma(msg, "generating parameters for P", prime);
  uint[] primes = [2, 3, 5, 7, 11, 13, 17, 19, 23];

  // Compute PG's modulus.
  uint modpg = 1;
  foreach (prm; primes) { modpg *= prm; if (prm == prime) break; }

  // Generate PG's residue values.
  uint[] residues;
  uint pc  = 5;
  uint inc = 2;
  while (pc < modpg / 2) {
    if (gcd(modpg, pc) == 1) {residues ~= pc; residues ~= modpg - pc;}
    pc += inc;
    inc = inc ^ 0b110;
  }
  residues = sort(residues).array;
  residues ~= modpg - 1;
  residues ~= modpg + 1;
  auto rescnt = residues.length;    // PG's residues count

  // Extract upper twinpair residues here.
  uint[] restwins;
  uint j = 0;
  while (j < rescnt - 1) {
    if (residues[j] + 2 == residues[j + 1]) {restwins ~= residues[j + 1]; ++j;}
    ++j;
  }
  auto twinpairs = restwins.length; // twinpairs count

  // Create PG's residues inverses here.
  uint[] inverses;
  foreach (res; residues) {inverses ~= modInv(res, modpg);}

  return PgParameters(modpg, rescnt, twinpairs, residues, restwins, inverses);
}

// Generate at compile time the parameters for PGs.
enum parametersp5  = genPgParameters(5);
enum parametersp7  = genPgParameters(7);
enum parametersp11 = genPgParameters(11);
enum parametersp13 = genPgParameters(13);
// TODO: Discover why this causes compilation errors.
//immutable parametersp17 = genPGparameters!(17);

// Global parameters
shared uint pcnt;             // Number of primes from r1..sqrt(N)
shared ulong num;             // Adjusted (odd) input value
shared ulong twinscnt;        // Number of twinprimes <= N
shared ulong[] primes;        // List of primes r1..sqrt(N)
shared uint kb = 0;           // Segment size for each seg restrack
shared uint[] cnts;           // Hold twinprime counts for seg bytes
shared ulong[] lastwins;      // Holds last twin <= num in each thread
shared uint[] pos;            // Convert residue val to its residues index val
                              // faster than `residues.find(residue)
shared PgParameters pgParameters;
shared uint modpg;            // PG's modulus value
shared uint rescnt;           // PG's residues count
shared uint pairscnt;         // PG's twinpairs count
shared uint[] residues;       // PS's list of residues
shared uint[] restwins;       // PG's list of twinpair residues
shared uint[] resinvrs;       // PG's list of residues inverses
shared uint bn;               // Segment size factor for PG and input number

/**
 * Select at runtime best PG and segment size factor to use for input value.
 * These are good estimates derived from PG data profiling. Can be improved.
 */
void selectPg(ulong num) {
  if (num < 10_000_000) {
    pgParameters = parametersp5;
    bn = 16;
  } else if (num < 1_100_000_000) {
    pgParameters = parametersp7;
    bn = 32;
  } else if (num < 35_500_000_000uL) {
    pgParameters = parametersp11;
    bn = 64;
  } else /*if (num < 15_000_000_000_000uL)*/ {
    pgParameters = parametersp13;
    if      (num > 7_000_000_000_000uL) { bn = 384; }
    else if (num > 2_500_000_000_000uL) { bn = 320; }
    else if (num >   250_000_000_000uL) { bn = 196; }
    else {bn = 96;}
    }
  /* else {
    // TODO: Fix when parametersp17 is properly computed.
    // pgParameters = PgParameters(parametersp17);
    pgParameters = parametersp13;
    bn = 384;
  }*/
  // Initialize parameters for selected PG.
  modpg    = pgParameters.modulus;
  rescnt   = cast(uint) pgParameters.residueCount;
  pairscnt = cast(uint) pgParameters.twinPairsCount;
  residues = pgParameters.residues;
  restwins = pgParameters.residueTwinPairs;
  resinvrs = pgParameters.residueInverses;
  cnts = new uint[](pairscnt);            // twinprime sums for seg bytes
  pos  = new uint[](modpg);               // create modpg size array to
  foreach(i; 0 .. rescnt)                 // for each residue
    pos[residues[i] - 2] = cast(uint) i;  // convert residue val -> indx
  lastwins = new ulong[](pairscnt);       // Holds last twin per thread
}

/**
 * Use PG to finds primes upto val.
 * Compute the list of primes r1..sqrt(input_num), and store in global
 * 'primes' array, and store their count in global var 'pcnt'.
 * Any algorithm (fast|small) is usable. Here the SoZ for the PG is used.
 */
void sozPg(ulong val) {
  uint md = modpg;                  // PG's modulus value
  ulong rscnt = rescnt;             // PG's residue count
  shared const(uint[]) res = residues; // PG's residues list

  ulong num = (val - 1) | 1;        // if val even then subtract 1
  ulong k = num / md;               // compute its residue group value
  ulong modk = md * k;              // compute the resgroup base value
  uint r = 0;                       // from 1st residue in num's resgroup
  while (num >= modk + res[r]) ++r; // find last pc val|position <= num
  ulong maxpcs = k * rscnt + r;     // max number of prime candidates <= num
  bool[] prms = new bool[](maxpcs); // array of prime candidates set False

  ulong sqrtN = cast(ulong) sqrt(cast(double) num); // integer sqrt of num
  modk = 0;  r = -1;  k = 0;        // initialize sieve parameters

  // mark the multiples of the primes r1..sqrtN in 'prms'
  foreach (prm; prms) {             // from list of pc positions in prms
    ++r; if (r == rscnt) {r = 0; modk += md; ++k;}
    if (prm) continue;              // if pc not prime go to next location
    uint  prm_r = res[r];           // if prime save its residue value
    ulong prime = modk + prm_r;     // numerate the prime value
    if (prime > sqrtN) break;       // we're finished if it's > sqrtN
    ulong prmstep = prime * rscnt;  // prime's stepsize to mark its mults
    foreach (ri; res) {             // mark prime's multiples in prms
      uint prod = prm_r * ri - 2;   // compute cross-product for r|ri pair
      // compute resgroup val of 1st prime multiple for each restrack
      // starting there, mark all prime multiples on restrack upto end of prms
      ulong prm_mult = (k * (prime + ri) + prod / md) * rscnt + pos[prod % md];
      while (prm_mult < maxpcs) { prms[prm_mult] = true; prm_mult += prmstep; }
    }
  }
  // prms now contains the nonprime positions for the prime candidates r1..N
  // extract primes into global var 'primes' and count into global var 'pcnt'
  primes = [];                      // create empty dynamic array for primes
  modk = 0; r = -1;                 // initialize loop parameters
  foreach (prm; prms) {             // numerate|store primes from pcs list
    ++r; if (r == rscnt) {r = 0; modk += md;}
    if (!prm) primes ~= modk + res[r]; // put prime in global 'primes' list
  }
  pcnt = cast(uint) primes.length;     // set global count of primes
}

/*
 * Print twinprimes for given twinpair for given segment slice.
 * Primes will not be displayed in sorted order, collect|sort later for that.
void printprms(uint Kn, ulong Ki, uint indx, ubyte[] seg) {
  ulong modk = Ki * modpg;          // base val of 1st resgroup in slice
  uint res = restwins[indx];        // for hi tp residue value
  foreach (k; in 0 .. Kn {          // for each of Kn resgroups in slice
    if (seg[k] == 0) {              // if seg byte for resgroup has twinprime
      if (modk + res <= num) {      // and if upper twinprime <= num
        write(modk + res - 1, " "); // print twinprime mid val on a line
      }
    }
    modk += modpg;                  // set base value for next resgroup
  }
}
*/

/**
 * For 'nextp' array for given twinpair at 'indx' in 'restwins',
 * init each col w/1st prime multiple resgroup for the primes r1..sqrt(N).
 */
ulong[] nextp_init(int indx, ulong[] nextp) {
  uint r_hi = restwins[indx];            // upper twinpair value
  uint r_lo = r_hi - 2;                  // lower twinpair value
  uint row_lo = 0;                       // nextp addr for lower twinpair
  uint row_hi = pcnt;                    // nextp addr for upper twinpair
  foreach(size_t j, prime; primes) {     // for each primes r1..sqrt(N)
    auto k = (prime - 2) / modpg;        // find its resgroup
    auto r = (prime - 2) % modpg + 2;    // and its residue value
    auto r_inv = resinvrs[pos[r - 2]];   // and its residue inverse
    auto ri = (r_lo * r_inv - 2) % modpg + 2; // compute ri for r
    nextp[row_lo + j] = k * (prime + ri) + (r * ri - 2) / modpg;
    ri = (r_hi * r_inv - 2) % modpg + 2; // compute ri for r
    nextp[row_hi + j] = k * (prime + ri) + (r * ri - 2) / modpg;
  }
  return nextp;
}

/**
 * Perform in a thread, the ssoz for a given twinpair, for Kmax resgroups.
 * First create|init 'nextp' array of 1st prime mults for given twinpair, and
 * its seg array of KB bytes, which will be gc'd|recovered at end of thread.
 * For sieve, mark seg byte to '1' if either twinpair restrack is nonprime,
 * for primes mults resgroups, update 'nextp' restrack slices acccordingly.
 * Then find last twinprime|sum <= num, store sum in 'cnts' for this twinpair.
 * Can optionally compile to print mid twinprime values generated by twinpair.
 */
void twinsSieve(ulong Kmax, uint indx) {
  uint sum = 0;                        // init twins cnt|1st resgroup for slice
  ulong Ki = 0;                        // first resgroup val for each seg slice
  uint  Kn = 0;                        // resgroup seg size for each segment
  uint upk = 0;                        // resgroup val of largest tp in seg
  ulong hi_tp = 0;                     // value of largest tp hi pair in seg
  ubyte[] seg = new ubyte[](kb);       // create seg byte array for twin pair
  ulong[] nextp = new ulong[](pcnt*2); // create 1st mults array for twin pair
  nextp = nextp_init(indx, nextp);     // init w/1st prime mults for twin pair
  while (Ki < Kmax) {                  // for Kn resgroup size slices upto Kmax
    Kn = min(kb, Kmax - Ki);           // set segment slice resgroup length
    foreach (b; 0 .. Kn) seg[b] = 0;   // set all seg restrack bits to prime
    foreach (j, prime; primes) {       // for each prime index r1..sqrt(N)
                                       // for lower twin pair residue track
      ulong k = nextp[j];              // starting from this resgroup in 'seg'
      while (k < Kn) {                 // for each primenth byte to end of 'seg'
        seg[k] = seg[k] |  1;          // mark byte as not a twin prime
        k += prime;  }                 // compute next prime multiple resgroup
      nextp[j] = k - Kn;               // save 1st resgroup in next eligible seg
                                       // for upper twin pair residue track
      k = nextp[pcnt + j];             // starting from this resgroup in 'seg'
      while (k < Kn) {                 // for each primenth byte to end of 'seg'
        seg[k] = seg[k] | 1;           // mark byte as not a twin prime
        k += prime;  }                 // compute next prime multiple resgroup
      nextp[pcnt + j] = k - Kn;        // save 1st resgroup in next eligible seg
    }
    auto cnt = 0;                      // initialize segment twin primes count
    foreach (k; 0 .. Kn) if (seg[k] == 0) ++cnt; // sum segment twin primes
    if (cnt > 0) {                     // if segment has twin primes
      sum += cnt;                      // add the segment count to total count
      foreach (k; 1 .. Kn + 1)         // find location of largest twin prime
        if (seg[Kn - k] == 0) {upk = Kn - k; break;} // count down to largest tp
      lastwins[indx] = hi_tp;          // store hi_tp from previous segment
      ulong modk = (Ki + upk) * modpg; // modk for largest tp
      hi_tp = modk + restwins[indx];   // largest hi seg tp
    }
    // printprms(Kn, Ki, indx, seg)    // display twinprimes for this twinpair
    Ki += kb;                          // set 1st resgroup val of next seg slice
  }
                                       // see if largest tp in final seg in range
  if (hi_tp > num) {                   // if outside find sum|hi_tp that's inside
    foreach (k; 0 .. upk + 1) {        // count down from upk resgroup to '0'
      if (seg[upk - k] == 0) {         // if twin prime at seg resgroup address
          if (hi_tp <= num) {lastwins[indx] = hi_tp; break;} // store if in range
          --sum; }                     // else reduce sum for too large twin 
      hi_tp -= modpg;                  // then check next lower twin pair hi val
    }
  }
  else {lastwins[indx] = hi_tp;}       // store unadjusted final seg hi_tp value
  cnts[indx] = sum;                    // store correct(ed) sum for twin pair

}
/**
 * Perform in parallel segmented sieve for Kmax resgroups for each twin pair.
 * Then add segs twin primes sums from each twin pair thread to 'twinscnt'.
 */
void segsieve(ulong Kmax) {
  foreach (indx; parallel(iota(0, pairscnt))) {
    twinsSieve(Kmax, cast(uint) indx); // sieve a selected twinpair restracks
  }
  foreach (sum; cnts) twinscnt = twinscnt + sum; // update twinscnt w/seg sums
}

/**
 * Use selected Pn prime generator for SSoZ
 * Main routine to setup, perform, and display results for twinprimes sieve.
 */
void twinPrimesSsoz() {
  write("Enter integer number: ");
  ulong val;
  readf!"%d"(val);  // find primes <= val (13..2^64-1)

  writeln("\nthreads = ", totalCPUs);
  auto stopWatchSetup = StopWatch();
  stopWatchSetup.start(); // start timing sieve setup execution

  num = val - 1 |  1;     // if val even subtract 1
  selectPg(num);          // select PG and seg factor for input number
  auto k = num / modpg;   // compute its resgroup
  auto modk = modpg * k;  // compute its base num
  auto Kmax = (num - 2) / modpg + 1;  // max num of resgroups
  auto b = bn * 1024;     // set seg size to optimize for selected PG
  kb = cast(uint)(Kmax < b ? Kmax + 1 : b);  // min num of segment resgroups

  writeln("each thread segment is [", 1, " x ", kb, "] bytes array");

  // This is not necessary for running the program but provides information
  // to determine the 'efficiency' of the used PG: (num of primes)/(num of pcs)
  // The closer the ratio is to '1' the higher the PG's 'efficiency'.
  uint r = 0;            // from first residue in last resgroup
  while (num >= modk + restwins[r]) ++r;  // find last tp index <= num

  auto maxpairs = k * pairscnt + r;       // maximum number of twinpairs <= num

  writeln("twinprime candidates = ", maxpairs, "; resgroups = ", Kmax);

  sozPg(cast(ulong) sqrt(cast(double) num)); // compute pcnt|primes <= sqrt(num)

  writeln("each ", pairscnt, " threads has nextp[", 2, " x ", pcnt, "] array");
  stopWatchSetup.stop();  // sieve setup time
  writeln("setup time = ", stopWatchSetup.peek);

  // 1st 4 twinprime counts
  if      (modpg > 30030) { twinscnt = 4; }
  else if (modpg > 210)   { twinscnt = 3; }
  else                    { twinscnt = 2; }
  writeln("perform twinprimes ssoz sieve"); // start doing ssoz now

  auto stopWatchExecution = StopWatch();  // start timing ssoz sieve execution
  stopWatchExecution.start();
  segsieve(cast(ulong) Kmax);             // perform total twinprime ssoz sieve
  ulong ltwin = maxElement(lastwins);     // find last twinprime, and its count
  auto Kn = Kmax % kb;                    // set num of resgroups in last slice
  if (Kn == 0) Kn = kb;                   // if mult of segsize set to seg size
  stopWatchExecution.stop();              // sieve execution time

  writeln("sieve time = ", stopWatchExecution.peek());
  writeln("last segment = ", Kn, " resgroups; segment slices = ", Kmax / kb + 1);
  writeln("total twins = ", twinscnt, "; last twin = ", ltwin - 1, "+/-1");
  writeln("total time = ", stopWatchSetup.peek() + stopWatchExecution.peek());
}

void main()
{
  twinPrimesSsoz();
}