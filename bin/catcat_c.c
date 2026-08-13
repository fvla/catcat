/* catcat's C boundary — real libc, really linked.
 *
 * These are the only foreign functions `extern` can reach today. A fixed table
 * rather than a dynamic `dlsym`, and that is a deliberate stopping point, not
 * an oversight: calling an arbitrary symbol with an arbitrary signature needs
 * libffi to build a call frame at runtime, which is a dependency and a large
 * surface for a demonstration whose point is that the EFFECT SYSTEM carries
 * foreign calls. The catcat-visible side — `extern`, the `!C !Unsafe` row, the
 * host as outermost handler — is identical either way; swapping this table for
 * libffi changes nothing above `perform` in bin/catcat.ml.
 *
 * Marshalling is the obvious one. catcat `i64` is OCaml `int` (boxed to Z on
 * the F* side and unboxed before it reaches here); catcat `str` is an OCaml
 * string, passed as `const char *`. Nothing else crosses, which
 * `E06.c_marshalable` enforces at the declaration.
 *
 * Every function here is `noalloc`-unsafe in the OCaml sense — `caml_copy_string`
 * allocates — so none of them is declared `[@@noalloc]` on the OCaml side.
 */

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

/* ( str -- i64 ) */
CAMLprim value catcat_c_strlen(value s)
{
  return Val_long((long) strlen(String_val(s)));
}

/* ( str -- i64 )  writes the string and a newline, as libc puts does.
 *
 * The fflush is not politeness. C stdio and OCaml's Stdlib buffer separately,
 * so without it `"a" print "b" puts` emits them in the wrong order — a real
 * confusion for anyone using this to check that the foreign call happened. */
CAMLprim value catcat_c_puts(value s)
{
  int r = puts(String_val(s));
  fflush(stdout);
  return Val_long((long) r);
}

/* ( i64 -- i64 ) */
CAMLprim value catcat_c_abs(value n)
{
  return Val_long((long) abs((int) Long_val(n)));
}

/* ( -- i64 )  seconds since the epoch. */
CAMLprim value catcat_c_time(value unit)
{
  (void) unit;
  return Val_long((long) time(NULL));
}

/* ( -- i64 ) */
CAMLprim value catcat_c_getpid(value unit)
{
  (void) unit;
  return Val_long((long) getpid());
}

/* ( str -- str )  the empty string when unset; catcat has no option type yet,
 * which is the same concession `parse` makes and is documented alongside it. */
CAMLprim value catcat_c_getenv(value name)
{
  CAMLparam1(name);
  const char *v = getenv(String_val(name));
  CAMLreturn(caml_copy_string(v == NULL ? "" : v));
}
