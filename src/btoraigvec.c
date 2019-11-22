/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraigvec.h"
#include "btorcore.h"
#include "btoropt.h"
#include "utils/btoraigmap.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

static BtorAIGVec *
new_aigvec (BtorAIGVecMgr *avmgr, uint32_t width)
{
  assert (avmgr);
  assert (width > 0);

  BtorAIGVec *result;

  result        = btor_mem_malloc (avmgr->btor->mm,
                            sizeof (BtorAIGVec) + sizeof (BtorAIG *) * width);
  result->width = width;
  avmgr->cur_num_aigvecs++;
  if (avmgr->max_num_aigvecs < avmgr->cur_num_aigvecs)
    avmgr->max_num_aigvecs = avmgr->cur_num_aigvecs;
  return result;
}

BtorAIGVec *
btor_aigvec_const (BtorAIGVecMgr *avmgr, const BtorBitVector *bits)
{
  assert (avmgr);
  assert (bits);

  BtorAIGVec *result;
  uint32_t i, width;
  width = btor_bv_get_width (bits);
  assert (width > 0);
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] =
        !btor_bv_get_bit (bits, width - 1 - i) ? BTOR_AIG_FALSE : BTOR_AIG_TRUE;
  return result;
}

BtorAIGVec *
btor_aigvec_var (BtorAIGVecMgr *avmgr, uint32_t width)
{
  assert (avmgr);
  assert (width > 0);

  BtorAIGVec *result;
  uint32_t i;

  result = new_aigvec (avmgr, width);
  for (i = 1; i <= width; i++)
    result->aigs[width - i] = btor_aig_var (avmgr->amgr);
  return result;
}

void
btor_aigvec_invert (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  uint32_t i, width;
  (void) avmgr;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  width = av->width;
  for (i = 0; i < width; i++) av->aigs[i] = BTOR_INVERT_AIG (av->aigs[i]);
}

BtorAIGVec *
btor_aigvec_not (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  width  = av->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_not (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_slice (BtorAIGVecMgr *avmgr,
                   BtorAIGVec *av,
                   uint32_t upper,
                   uint32_t lower)
{
  BtorAIGVec *result;
  uint32_t i, width, diff, counter;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  assert (upper < av->width);
  assert (lower <= upper);
  counter = 0;
  width   = av->width;
  diff    = upper - lower;
  result  = new_aigvec (avmgr, diff + 1);
  for (i = width - upper - 1; i <= width - upper - 1 + diff; i++)
    result->aigs[counter++] = btor_aig_copy (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_and (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  width  = av1->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_and (avmgr->amgr, av1->aigs[i], av2->aigs[i]);
  return result;
}

static BtorAIG *
lt_aigvec(BtorAIGMgr *amgr,
  BtorAIG **v1, BtorAIG **v2, size_t count)
{
  BtorAIG *res, *tmp, *term0, *term1;
  res  = BTOR_AIG_FALSE;
  v1 += count;
  v2 += count;
  for (; count != 0; --count, --v1, --v2)
  {
    term0 = btor_aig_and (amgr, v1[-1], BTOR_INVERT_AIG (v2[-1]));

    tmp = btor_aig_and (amgr, BTOR_INVERT_AIG (term0), res);
    btor_aig_release (amgr, term0);
    btor_aig_release (amgr, res);
    res = tmp;

    term1 = btor_aig_and (amgr, BTOR_INVERT_AIG (v1[-1]), v2[-1]);

    tmp = btor_aig_or (amgr, term1, res);
    btor_aig_release (amgr, term1);
    btor_aig_release (amgr, res);
    res = tmp;
  }

  return res;
}

static void
lt_aigvec_NC1_recurse_impl(BtorAIGMgr *amgr,
  BtorAIG **v1, BtorAIG **v2, size_t count,
  BtorAIG **lt, BtorAIG **leq)
{
  size_t half;
  BtorAIG *hi_lt, *hi_leq, *lo_lt, *lo_leq, *tmp;
  if (count == 1)
  {
    *lt = btor_aig_and(amgr, BTOR_INVERT_AIG(*v1), *v2);
    *leq = btor_aig_or(amgr, BTOR_INVERT_AIG(*v1), *v2);
    return;
  }
  half = (count >> 1);
  lt_aigvec_NC1_recurse_impl(amgr,
    v1, v2, half,
    &hi_lt, &hi_leq);
  lt_aigvec_NC1_recurse_impl(amgr,
    v1 + half, v2 + half, count - half,
    &lo_lt, &lo_leq);
  /* lt = hi_lt || (hi_leq && lo_lt). */
  tmp = btor_aig_and(amgr, hi_leq, lo_lt);
  *lt = btor_aig_or(amgr, hi_lt, tmp);
  btor_aig_release(amgr, tmp);
  /* leq = hi_leq && lo_leq. */
  *leq = btor_aig_and(amgr, hi_leq, lo_leq);
  /* Clean up. */
  btor_aig_release(amgr, hi_lt);
  btor_aig_release(amgr, hi_leq);
  btor_aig_release(amgr, lo_lt);
  btor_aig_release(amgr, lo_leq);
}

static BtorAIG *
lt_aigvec_NC1_recurse(BtorAIGMgr *amgr,
  BtorAIG **v1, BtorAIG **v2, size_t count)
{
  BtorAIG *lt, *leq;
  lt_aigvec_NC1_recurse_impl(amgr, v1, v2, count, &lt, &leq);
  btor_aig_release(amgr, leq);
  return lt;
}

static BtorAIG *
lt_aigvec_NC1_norecurse(BtorAIGMgr *amgr,
  BtorAIG **v1, BtorAIG **v2, size_t count)
{
  size_t i, half;
  BtorAIG *lo_lt, *lo_leq, *hi_lt, *hi_leq, *tmp;
  /* GCC only, but who cares... */
  BtorAIG *lt[count], *leq[count];
  /* Due to reversal, MSB has the largest index. */
  for (i = 0, v1 += count, v2 += count; i != count; ++i, --v1, --v2)
  {
    lt[i] = btor_aig_and(amgr, BTOR_INVERT_AIG(v1[-1]), v2[-1]);
    leq[i] = btor_aig_or(amgr, BTOR_INVERT_AIG(v1[-1]), v2[-1]);
  }
  while (count != 1)
  {
    half = (count >> 1);
    for (i = 0; i != half; ++i)
    {
      lo_lt = lt[i << 1];
      lo_leq = leq[i << 1];
      hi_lt = lt[(i << 1) | 1];
      hi_leq = leq[(i << 1) | 1];
      /* lt = hi_lt || (hi_leq && lo_lt). */
      tmp = btor_aig_and(amgr, hi_leq, lo_lt);
      lt[i] = btor_aig_or(amgr, hi_lt, tmp);
      btor_aig_release(amgr, tmp);
      /* leq = hi_leq && lo_leq. */
      leq[i] = btor_aig_and(amgr, hi_leq, lo_leq);
      /* Clean up. */
      btor_aig_release(amgr, hi_lt);
      btor_aig_release(amgr, hi_leq);
      btor_aig_release(amgr, lo_lt);
      btor_aig_release(amgr, lo_leq);
    }
    if ((count & 1))
    {
      lt[half] = lt[half << 1];
      leq[half] = leq[half << 1];
      ++half;
    }
    count = half;
  }
  btor_aig_release(amgr, *leq);
  return *lt;
}

BtorAIGVec *
btor_aigvec_ult (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  result          = new_aigvec (avmgr, 1);
  result->aigs[0] = lt_aigvec_NC1_recurse(avmgr->amgr,
    av1->aigs, av2->aigs, av1->width);
  return result;
}

static BtorAIG *
eq_aigvec(BtorAIGMgr *amgr,
  BtorAIG **v1, BtorAIG **v2, size_t count)
{
  BtorAIG *eq, *tmp1, *tmp2;
  eq = btor_aig_eq(amgr, *v1, *v2);
  for (--count, ++v1, ++v2; count != 0; --count, ++v1, ++v2)
  {
    tmp1 = eq;
    tmp2 = btor_aig_eq(amgr, *v1, *v2);
    eq = btor_aig_and(amgr, tmp1, tmp2);
    btor_aig_release(amgr, tmp1);
    btor_aig_release(amgr, tmp2);
  }
  return eq;
}

static BtorAIG *
eq_aigvec_NC1_recurse(BtorAIGMgr *amgr,
  BtorAIG **v1, BtorAIG **v2, size_t count)
{
  size_t half;
  BtorAIG *eq1, *eq2, *eq;
  if (count == 1)
  {
    return btor_aig_eq(amgr, *v1, *v2);
  }
  half = (count >> 1);
  eq1 = eq_aigvec_NC1_recurse(amgr, v1, v2, half);
  eq2 = eq_aigvec_NC1_recurse(amgr, v1 + half, v2 + half, count - half);
  eq = btor_aig_and(amgr, eq1, eq2);
  btor_aig_release(amgr, eq1);
  btor_aig_release(amgr, eq2);
  return eq;
}

static BtorAIG *
eq_aigvec_NC1_norecurse(BtorAIGMgr *amgr,
  BtorAIG **v1, BtorAIG **v2, size_t count)
{
  size_t i, half;
  /* GCC only, but who cares... */
  BtorAIG *eq[count], *eq1, *eq2;
  for (i = 0; i != count; ++i)
  {
    eq[i] = btor_aig_eq(amgr, *(v1++), *(v2++));
  }
  while (count != 1)
  {
    half = (count >> 1);
    for (i = 0; i != half; ++i)
    {
      eq1 = eq[i << 1];
      eq2 = eq[(i << 1) | 1];
      eq[i] = btor_aig_and(amgr, eq1, eq2);
      btor_aig_release(amgr, eq1);
      btor_aig_release(amgr, eq2);
    }
    if ((count & 1))
    {
      eq[half] = eq[half << 1];
      ++half;
    }
    count = half;
  }
  return *eq;
}

BtorAIGVec *
btor_aigvec_eq (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  result     = new_aigvec (avmgr, 1);
  result->aigs[0] = eq_aigvec(avmgr->amgr, av1->aigs, av2->aigs, av1->width);
  return result;
}

static BtorAIG *
half_adder (BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG **cout)
{
  BtorAIG *res, *x_and_y, *not_x, *not_y, *not_x_and_not_y, *x_xnor_y;
  x_and_y         = btor_aig_and (amgr, x, y);
  not_x           = BTOR_INVERT_AIG (x);
  not_y           = BTOR_INVERT_AIG (y);
  not_x_and_not_y = btor_aig_and (amgr, not_x, not_y);
  x_xnor_y        = btor_aig_or (amgr, x_and_y, not_x_and_not_y);
  res             = BTOR_INVERT_AIG (x_xnor_y);
  *cout           = x_and_y;
  btor_aig_release (amgr, not_x_and_not_y);
  return res;
}

static BtorAIG *
full_adder (
    BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG *cin, BtorAIG **cout)
{
  BtorAIG *sum, *c1, *c2, *res;
  sum   = half_adder (amgr, x, y, &c1);
  res   = half_adder (amgr, sum, cin, &c2);
  *cout = btor_aig_or (amgr, c1, c2);
  btor_aig_release (amgr, sum);
  btor_aig_release (amgr, c1);
  btor_aig_release (amgr, c2);
  return res;
}

static int32_t
compare_aigvec_lsb_first (BtorAIGVec *a, BtorAIGVec *b)
{
  uint32_t width, i;
  int32_t res;
  assert (a);
  assert (b);
  width = a->width;
  assert (width == b->width);
  res = 0;
  for (i = 0; !res && i < width; i++)
    res = btor_aig_compare (a->aigs[i], b->aigs[i]);
  return res;
}

/* Computes X+Y, X+Y+1,
 * replaces X by X+Y, Y by X+Y+1,
 * and saves the carry bits in c0, c1.
 * Doesn't assume ownership of old values in X, Y.
 */
static void
add_aigvec_recurse_impl(BtorAIGMgr *amgr,
  BtorAIG **x, BtorAIG **y,
  BtorAIG **c0, BtorAIG **c1,
  size_t count)
{
  size_t half, i;
  BtorAIG *t1, *t2, *cl0, *cl1, *ch0, *ch1;
  BtorAIG *vh0, *vh1;
  if (count == 1)
  {
    t1 = btor_aig_eq(amgr, *x, *y);
    *c0 = btor_aig_and(amgr, *x, *y);
    *c1 = btor_aig_or(amgr, *x, *y);
    *x = btor_aig_not(amgr, t1);
    *y = t1;
    return;
  }
  /* Add the lower half. */
  half = (count >> 1);
  add_aigvec_recurse_impl(amgr, x, y, &cl0, &cl1, half);
  /* Add the upper half without considering the carry from the lower half. */
  add_aigvec_recurse_impl(amgr, x += half, y += half,
    &ch0, &ch1, count -= half);
  /* Adjust the upper half according to the carry from the lower half. */
  for (i = 0; i != count; ++i)
  {
    /* Select high part of X+Y. */
    t1 = btor_aig_and(amgr, BTOR_INVERT_AIG(cl0), *x);
    t2 = btor_aig_and(amgr, cl0, *y);
    vh0 = btor_aig_or(amgr, t1, t2);
    btor_aig_release(amgr, t1);
    btor_aig_release(amgr, t2);
    /* Select high part of X+Y+1. */
    t1 = btor_aig_and(amgr, BTOR_INVERT_AIG(cl1), *x);
    t2 = btor_aig_and(amgr, cl1, *y);
    vh1 = btor_aig_or(amgr, t1, t2);
    btor_aig_release(amgr, t1);
    btor_aig_release(amgr, t2);
    /* Replace by the correct values. */
    *(x++) = vh0;
    *(y++) = vh1;
  }
  /* Select the carry bit of X+Y. */
  t1 = btor_aig_and(amgr, BTOR_INVERT_AIG(cl0), ch0);
  t2 = btor_aig_and(amgr, cl0, ch1);
  *c0 = btor_aig_or(amgr, t1, t2);
  btor_aig_release(amgr, t1);
  btor_aig_release(amgr, t2);
  /* Select the carry bit of X+Y+1. */
  t1 = btor_aig_and(amgr, BTOR_INVERT_AIG(cl1), ch0);
  t2 = btor_aig_and(amgr, cl1, ch1);
  *c1 = btor_aig_or(amgr, t1, t2);
  btor_aig_release(amgr, t1);
  btor_aig_release(amgr, t2);
  /* Clean up. */
  btor_aig_release(amgr, ch0);
  btor_aig_release(amgr, ch1);
  btor_aig_release(amgr, cl0);
  btor_aig_release(amgr, cl1);
}

static void
add_aigvec_recurse(BtorAIGMgr *amgr,
  BtorAIG **x, BtorAIG **y, BtorAIG **z,
  size_t count)
{
  /* GCC only, but who cares... */
  BtorAIG *xx[count], *yy[count];
  BtorAIG *c0, *c1;
  size_t i;
  for (i = 0, x += count, y += count; i != count; ++i)
  {
    xx[i] = *(--x);
    yy[i] = *(--y);
  }
  add_aigvec_recurse_impl(amgr, xx, yy, &c0, &c1, count);
  btor_aig_release(amgr, c0);
  btor_aig_release(amgr, c1);
  for (i = 0, z += count; i != count; ++i)
  {
    *(--z) = xx[i];
    btor_aig_release(amgr, yy[i]);
  }
}

static void
add_aigvec_naive(BtorAIGMgr *amgr,
  BtorAIG **x, BtorAIG **y, BtorAIG **z,
  size_t count)
{
  BtorAIG *cout, *cin;
  uint32_t i, j;
  cout = cin = BTOR_AIG_FALSE;
  for (j = 1, i = count - 1; j <= count; j++, i--)
  {
    z[i] = full_adder (amgr, x[i], y[i], cin, &cout);
    btor_aig_release (amgr, cin);
    cin = cout;
  }
  btor_aig_release (amgr, cout);
}


BtorAIGVec *
btor_aigvec_add (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);

  BtorAIGVec *result;

  if (btor_opt_get (avmgr->btor, BTOR_OPT_SORT_AIGVEC) > 0
      && compare_aigvec_lsb_first (av1, av2) > 0)
  {
    BTOR_SWAP (BtorAIGVec *, av1, av2);
  }

  result = new_aigvec (avmgr, av1->width);
  add_aigvec_recurse(avmgr->amgr,
    av1->aigs, av2->aigs, result->aigs,
    av1->width);
  return result;
}

static BtorAIGVec *
sll_n_bits_aigvec (BtorAIGVecMgr *avmgr,
                   BtorAIGVec *av,
                   uint32_t n,
                   BtorAIG *shift)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *and1, *and2, *not_shift;
  uint32_t i, j, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  assert (n < av->width);
  if (n == 0) return btor_aigvec_copy (avmgr, av);
  amgr      = avmgr->amgr;
  width     = av->width;
  not_shift = btor_aig_not (amgr, shift);
  result    = new_aigvec (avmgr, width);
  for (i = 0; i < width - n; i++)
  {
    and1            = btor_aig_and (amgr, av->aigs[i], not_shift);
    and2            = btor_aig_and (amgr, av->aigs[i + n], shift);
    result->aigs[i] = btor_aig_or (amgr, and1, and2);
    btor_aig_release (amgr, and1);
    btor_aig_release (amgr, and2);
  }
  for (j = width - n; j < width; j++)
    result->aigs[j] = btor_aig_and (amgr, av->aigs[j], not_shift);
  btor_aig_release (amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_aigvec_sll (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result, *temp;
  uint32_t i, j, width;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width > 1);
  assert (btor_util_is_power_of_2 (av1->width));
  assert (btor_util_log_2 (av1->width) == av2->width);
  width  = av2->width;
  result = sll_n_bits_aigvec (avmgr, av1, 1, av2->aigs[av2->width - 1]);
  for (j = 2, i = width - 2; j <= width; j++, i--)
  {
    temp   = result;
    result = sll_n_bits_aigvec (
        avmgr, temp, btor_util_pow_2 (width - i - 1), av2->aigs[i]);
    btor_aigvec_release_delete (avmgr, temp);
  }
  return result;
}

static BtorAIGVec *
srl_n_bits_aigvec (BtorAIGVecMgr *avmgr,
                   BtorAIGVec *av,
                   uint32_t n,
                   BtorAIG *shift)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  BtorAIG *and1, *and2, *not_shift;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  assert (n < av->width);
  if (n == 0) return btor_aigvec_copy (avmgr, av);
  amgr      = avmgr->amgr;
  width     = av->width;
  not_shift = btor_aig_not (amgr, shift);
  result    = new_aigvec (avmgr, width);
  for (i = 0; i < n; i++)
    result->aigs[i] = btor_aig_and (amgr, av->aigs[i], not_shift);
  for (i = n; i < width; i++)
  {
    and1            = btor_aig_and (amgr, av->aigs[i], not_shift);
    and2            = btor_aig_and (amgr, av->aigs[i - n], shift);
    result->aigs[i] = btor_aig_or (amgr, and1, and2);
    btor_aig_release (amgr, and1);
    btor_aig_release (amgr, and2);
  }
  btor_aig_release (amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_aigvec_srl (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result, *temp;
  uint32_t i, j, width;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width > 1);
  assert (btor_util_is_power_of_2 (av1->width));
  assert (btor_util_log_2 (av1->width) == av2->width);
  width  = av2->width;
  result = srl_n_bits_aigvec (avmgr, av1, 1, av2->aigs[av2->width - 1]);
  for (j = 2, i = width - 2; j <= width; j++, i--)
  {
    temp   = result;
    result = srl_n_bits_aigvec (
        avmgr, temp, btor_util_pow_2 (width - i - 1), av2->aigs[i]);
    btor_aigvec_release_delete (avmgr, temp);
  }
  return result;
}

static BtorAIGVec *
mul_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  BtorAIG *cin, *cout, *and, *tmp;
  BtorAIGMgr *amgr;
  BtorAIGVec *res;
  uint32_t i, j, k, ik, jk, width;

  width = a->width;
  amgr  = btor_aigvec_get_aig_mgr (avmgr);

  assert (width > 0);
  assert (width == b->width);

  if (btor_opt_get (avmgr->btor, BTOR_OPT_SORT_AIGVEC) > 0
      && compare_aigvec_lsb_first (a, b) > 0)
  {
    BTOR_SWAP (BtorAIGVec *, a, b);
  }

  res = new_aigvec (avmgr, width);

  for (k = 0; k < width; k++)
    res->aigs[k] = btor_aig_and (amgr, a->aigs[k], b->aigs[width - 1]);

  for (ik = 2, i = width - 2; ik <= width; ik++, i--)
  {
    cout = BTOR_AIG_FALSE;
    for (jk = 0, j = i; jk <= i; jk++, j--)
    {
      and = btor_aig_and (amgr, a->aigs[width - 1 - i + j], b->aigs[i]);
      tmp = res->aigs[j];
      cin = cout;
      res->aigs[j] = full_adder (amgr, tmp, and, cin, &cout);
      btor_aig_release (amgr, and);
      btor_aig_release (amgr, tmp);
      btor_aig_release (amgr, cin);
    }
    btor_aig_release (amgr, cout);
  }

  return res;
}

BtorAIGVec *
btor_aigvec_mul (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  return mul_aigvec (avmgr, a, b);
}

static void
SC_GATE_CO_aigvec (
    BtorAIGMgr *amgr, BtorAIG **CO, BtorAIG *R, BtorAIG *D, BtorAIG *CI)
{
  BtorAIG *D_or_CI, *D_and_CI, *M;
  D_or_CI  = btor_aig_or (amgr, D, CI);
  D_and_CI = btor_aig_and (amgr, D, CI);
  M        = btor_aig_and (amgr, D_or_CI, R);
  *CO      = btor_aig_or (amgr, M, D_and_CI);
  btor_aig_release (amgr, D_or_CI);
  btor_aig_release (amgr, D_and_CI);
  btor_aig_release (amgr, M);
}

static void
SC_GATE_S_aigvec (BtorAIGMgr *amgr,
                  BtorAIG **S,
                  BtorAIG *R,
                  BtorAIG *D,
                  BtorAIG *CI,
                  BtorAIG *Q)
{
  BtorAIG *D_and_CI, *D_or_CI;
  BtorAIG *T2_or_R, *T2_and_R;
  BtorAIG *T1, *T2;
  D_or_CI  = btor_aig_or (amgr, D, CI);
  D_and_CI = btor_aig_and (amgr, D, CI);
  T1       = btor_aig_and (amgr, D_or_CI, BTOR_INVERT_AIG (D_and_CI));
  T2       = btor_aig_and (amgr, T1, Q);
  T2_or_R  = btor_aig_or (amgr, T2, R);
  T2_and_R = btor_aig_and (amgr, T2, R);
  *S       = btor_aig_and (amgr, T2_or_R, BTOR_INVERT_AIG (T2_and_R));
  btor_aig_release (amgr, T1);
  btor_aig_release (amgr, T2);
  btor_aig_release (amgr, D_and_CI);
  btor_aig_release (amgr, D_or_CI);
  btor_aig_release (amgr, T2_and_R);
  btor_aig_release (amgr, T2_or_R);
}

static void
udiv_urem_aigvec (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *Ain,
                  BtorAIGVec *Din,
                  BtorAIGVec **Qptr,
                  BtorAIGVec **Rptr)
{
  BtorAIG **A, **nD, ***S, ***C;
  BtorAIGVec *Q, *R;
  BtorAIGMgr *amgr;
  BtorMemMgr *mem;
  uint32_t size, i, j;

  size = Ain->width;
  assert (size > 0);

  amgr = btor_aigvec_get_aig_mgr (avmgr);
  mem  = avmgr->btor->mm;

  BTOR_NEWN (mem, A, size);
  for (i = 0; i < size; i++) A[i] = Ain->aigs[size - 1 - i];

  BTOR_NEWN (mem, nD, size);
  for (i = 0; i < size; i++) nD[i] = BTOR_INVERT_AIG (Din->aigs[size - 1 - i]);

  BTOR_NEWN (mem, S, size + 1);
  for (j = 0; j <= size; j++)
  {
    BTOR_NEWN (mem, S[j], size + 1);
    for (i = 0; i <= size; i++) S[j][i] = BTOR_AIG_FALSE;
  }

  BTOR_NEWN (mem, C, size + 1);
  for (j = 0; j <= size; j++)
  {
    BTOR_NEWN (mem, C[j], size + 1);
    for (i = 0; i <= size; i++) C[j][i] = BTOR_AIG_FALSE;
  }

  R = new_aigvec (avmgr, size);
  Q = new_aigvec (avmgr, size);

  for (j = 0; j <= size - 1; j++)
  {
    S[j][0] = btor_aig_copy (amgr, A[size - j - 1]);
    C[j][0] = BTOR_AIG_TRUE;

    for (i = 0; i <= size - 1; i++)
      SC_GATE_CO_aigvec (amgr, &C[j][i + 1], S[j][i], nD[i], C[j][i]);

    Q->aigs[j] = btor_aig_or (amgr, C[j][size], S[j][size]);

    for (i = 0; i <= size - 1; i++)
      SC_GATE_S_aigvec (
          amgr, &S[j + 1][i + 1], S[j][i], nD[i], C[j][i], Q->aigs[j]);
  }

  for (i = size; i >= 1; i--)
    R->aigs[size - i] = btor_aig_copy (amgr, S[size][i]);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_aig_release (amgr, C[j][i]);
    BTOR_DELETEN (mem, C[j], size + 1);
  }
  BTOR_DELETEN (mem, C, size + 1);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_aig_release (amgr, S[j][i]);
    BTOR_DELETEN (mem, S[j], size + 1);
  }
  BTOR_DELETEN (mem, S, size + 1);

  BTOR_DELETEN (mem, nD, size);
  BTOR_DELETEN (mem, A, size);

  *Qptr = Q;
  *Rptr = R;
}

BtorAIGVec *
btor_aigvec_udiv (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient  = 0;
  BtorAIGVec *remainder = 0;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_aigvec_release_delete (avmgr, remainder);
  return quotient;
}

BtorAIGVec *
btor_aigvec_urem (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient, *remainder;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width == av2->width);
  assert (av1->width > 0);
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_aigvec_release_delete (avmgr, quotient);
  return remainder;
}

BtorAIGVec *
btor_aigvec_concat (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  uint32_t i, pos, len_av1, len_av2;
  assert (avmgr);
  assert (av1);
  assert (av2);
  assert (av1->width > 0);
  assert (av2->width > 0);
  assert (INT32_MAX - av1->width >= av2->width);
  pos     = 0;
  amgr    = avmgr->amgr;
  len_av1 = av1->width;
  len_av2 = av2->width;
  result  = new_aigvec (avmgr, len_av1 + len_av2);
  for (i = 0; i < len_av1; i++)
    result->aigs[pos++] = btor_aig_copy (amgr, av1->aigs[i]);
  for (i = 0; i < len_av2; i++)
    result->aigs[pos++] = btor_aig_copy (amgr, av2->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_cond (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *av_cond,
                  BtorAIGVec *av_if,
                  BtorAIGVec *av_else)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av_cond);
  assert (av_if);
  assert (av_else);
  assert (av_cond->width == 1);
  assert (av_if->width == av_else->width);
  assert (av_if->width > 0);
  amgr   = avmgr->amgr;
  width  = av_if->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_cond (
        amgr, av_cond->aigs[0], av_if->aigs[i], av_else->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_copy (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGMgr *amgr;
  BtorAIGVec *result;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  amgr   = avmgr->amgr;
  width  = av->width;
  result = new_aigvec (avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = btor_aig_copy (amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_aigvec_clone (BtorAIGVec *av, BtorAIGVecMgr *avmgr)
{
  assert (av);
  assert (avmgr);

  uint32_t i;
  BtorAIGVec *res;
  BtorAIGMgr *amgr;
  BtorAIG *aig, *caig;

  amgr = avmgr->amgr;
  res  = new_aigvec (avmgr, av->width);
  for (i = 0; i < av->width; i++)
  {
    if (btor_aig_is_const (av->aigs[i]))
      res->aigs[i] = av->aigs[i];
    else
    {
      aig = av->aigs[i];
      assert (BTOR_REAL_ADDR_AIG (aig)->id >= 0);
      assert ((size_t) BTOR_REAL_ADDR_AIG (aig)->id
              < BTOR_COUNT_STACK (amgr->id2aig));
      caig = BTOR_PEEK_STACK (amgr->id2aig, BTOR_REAL_ADDR_AIG (aig)->id);
      assert (caig);
      assert (!btor_aig_is_const (caig));
      if (BTOR_IS_INVERTED_AIG (aig))
        res->aigs[i] = BTOR_INVERT_AIG (caig);
      else
        res->aigs[i] = caig;
      assert (res->aigs[i]);
    }
  }
  return res;
}

void
btor_aigvec_to_sat_tseitin (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGMgr *amgr;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  amgr = btor_aigvec_get_aig_mgr (avmgr);
  if (!btor_sat_is_initialized (amgr->smgr)) return;
  width = av->width;
  for (i = 0; i < width; i++) btor_aig_to_sat_tseitin (amgr, av->aigs[i]);
}

void
btor_aigvec_release_delete (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  uint32_t i, width;
  assert (avmgr);
  assert (av);
  assert (av->width > 0);
  mm    = avmgr->btor->mm;
  amgr  = avmgr->amgr;
  width = av->width;
  for (i = 0; i < width; i++) btor_aig_release (amgr, av->aigs[i]);
  btor_mem_free (mm, av, sizeof (BtorAIGVec) + sizeof (BtorAIG *) * av->width);
  avmgr->cur_num_aigvecs--;
}

BtorAIGVecMgr *
btor_aigvec_mgr_new (Btor *btor)
{
  assert (btor);

  BtorAIGVecMgr *avmgr;
  BTOR_CNEW (btor->mm, avmgr);
  avmgr->btor = btor;
  avmgr->amgr = btor_aig_mgr_new (btor);
  return avmgr;
}

BtorAIGVecMgr *
btor_aigvec_mgr_clone (Btor *btor, BtorAIGVecMgr *avmgr)
{
  assert (btor);
  assert (avmgr);

  BtorAIGVecMgr *res;
  BTOR_NEW (btor->mm, res);

  res->btor            = btor;
  res->amgr            = btor_aig_mgr_clone (btor, avmgr->amgr);
  res->max_num_aigvecs = avmgr->max_num_aigvecs;
  res->cur_num_aigvecs = avmgr->cur_num_aigvecs;
  return res;
}

void
btor_aigvec_mgr_delete (BtorAIGVecMgr *avmgr)
{
  assert (avmgr);
  btor_aig_mgr_delete (avmgr->amgr);
  BTOR_DELETE (avmgr->btor->mm, avmgr);
}

BtorAIGMgr *
btor_aigvec_get_aig_mgr (const BtorAIGVecMgr *avmgr)
{
  return avmgr ? avmgr->amgr : 0;
}
