// SPARC is a RISC ISA developed by Sun Microsystems.
//
// The byte order of the processor is big-endian. Anything larger than a
// byte is stored in the "reverse" order compared to little-endian
// processors such as x86-64.
//
// All instructions are 4 bytes long and aligned to 4 bytes boundaries.
//
// A notable feature of SPARC is that, unlike other RISC ISAs, it doesn't
// need range extension thunks. It is because the SPARC's CALL instruction
// contains a 30 bits immediate. The processor scales it by 4 to extend it
// to 32 bits (this is doable because all instructions are aligned to 4
// bytes boundaries, so the least significant two bits are always zero).
// That means CALL's reach is PC ± 2 GiB, elinating the need of range
// extension thunks. It comes with the cost that the CALL instruction alone
// takes 1/4th of the instruction encoding space, though.

#include "mold.h"

namespace mold::elf {

using E = SPARC64;

template <>
void PltSection<E>::copy_buf(Context<E> &ctx) {
  u8 *buf = ctx.buf + this->shdr.sh_offset;
  memset(buf, 0, this->shdr.sh_size);

  for (i64 i = 0; i < symbols.size(); i++) {
    Symbol<E> &sym = *symbols[i];
    ub32 *ent = (ub32 *)(buf + E::plt_hdr_size + i * E::plt_size);
    u64 addr = sym.get_plt_addr(ctx);

    // sethi (. - .PLT0), %g1
    ent[0] = 0x3000'0000 | ((ctx.plt->shdr.sh_addr - addr) >> 10);

    // ba,a  %xcc, .PLT1
    ent[1] = 0x3040'0000 | ((addr - ctx.plt->shdr.sh_addr + E::plt_size) >> 10);
  }
}

template <>
void PltGotSection<E>::copy_buf(Context<E> &ctx) {}

template <>
void EhFrameSection<E>::apply_reloc(Context<E> &ctx, const ElfRel<E> &rel,
                                    u64 offset, u64 val) {
  u8 *loc = ctx.buf + this->shdr.sh_offset + offset;

  switch (rel.r_type) {
  case R_NONE:
    return;
  default:
    Fatal(ctx) << "unknown relocation in ehframe: " << rel;
    return;
  }
  unreachable();
}

template <>
void InputSection<E>::apply_reloc_alloc(Context<E> &ctx, u8 *base) {
  ElfRel<E> *dynrel = nullptr;
  std::span<const ElfRel<E>> rels = get_rels(ctx);
  i64 frag_idx = 0;

  if (ctx.reldyn)
    dynrel = (ElfRel<E> *)(ctx.buf + ctx.reldyn->shdr.sh_offset +
                           file.reldyn_offset + this->reldyn_offset);

  for (i64 i = 0; i < rels.size(); i++) {
    const ElfRel<E> &rel = rels[i];
    if (rel.r_type == R_NONE)
      continue;

    Symbol<E> &sym = *file.symbols[rel.r_sym];
    u8 *loc = base + rel.r_offset;

    const SectionFragmentRef<E> *frag_ref = nullptr;
    if (rel_fragments && rel_fragments[frag_idx].idx == i)
      frag_ref = &rel_fragments[frag_idx++];

    auto check = [&](i64 val, i64 lo, i64 hi) {
      if (val < lo || hi <= val)
        Error(ctx) << *this << ": relocation " << rel << " against "
                   << sym << " out of range: " << val << " is not in ["
                   << lo << ", " << hi << ")";
    };

#define S   (frag_ref ? frag_ref->frag->get_addr(ctx) : sym.get_addr(ctx))
#define A   (frag_ref ? frag_ref->addend : this->get_addend(rel))
#define P   (output_section->shdr.sh_addr + offset + rel.r_offset)
#define G   (sym.get_got_addr(ctx) - ctx.got->shdr.sh_addr)
#define GOT ctx.got->shdr.sh_addr

    switch (rel.r_type) {
    case R_SPARC_5:
      *(ub32 *)loc |= bits(S + A, 4, 0);
      break;
    case R_SPARC_6:
      *(ub32 *)loc |= bits(S + A, 5, 0);
      break;
    case R_SPARC_7:
      *(ub32 *)loc |= bits(S + A, 6, 0);
      break;
    case R_SPARC_8:
      *(u8 *)loc = S + A;
      break;
    case R_SPARC_10:
      *(ub32 *)loc = S + A;
      break;
    case R_SPARC_11:
      *(ub32 *)loc = S + A;
      break;
    case R_SPARC_13:
      *(ub32 *)loc |= bits(S + A, 12, 0);
      break;
    case R_SPARC_22:
      *(ub32 *)loc |= bits(S + A, 21, 0);
      break;
    case R_SPARC_16:
    case R_SPARC_UA16:
      *(ub16 *)loc = S + A;
      break;
    case R_SPARC_32:
    case R_SPARC_UA32:
    case R_SPARC_PLT32:
      *(ub32 *)loc = S + A;
      break;
    case R_SPARC_64:
      apply_abs_dyn_rel(ctx, sym, rel, loc, S, A, P, dynrel);
      break;
    case R_SPARC_DISP8:
      *(u8 *)loc = S + A - P;
      break;
    case R_SPARC_DISP16:
      *(ub16 *)loc = S + A - P;
      break;
    case R_SPARC_DISP32:
    case R_SPARC_PCPLT32:
      *(ub32 *)loc = S + A - P;
      break;
    case R_SPARC_WDISP22:
      *(ub32 *)loc |= bits((S + A - P) >> 2, 21, 0);
      break;
    case R_SPARC_WDISP30:
    case R_SPARC_WPLT30:
      *(ub32 *)loc |= bits((S + A - P) >> 2, 29, 0);
      break;
    case R_SPARC_HI22:
    case R_SPARC_HIPLT22:
      *(ub32 *)loc |= bits((S + A) >> 10, 21, 0);
      break;
    case R_SPARC_LO10:
    case R_SPARC_LOPLT10:
      *(ub32 *)loc |= bits(S + A, 9, 0);
      break;
    case R_SPARC_GOT10:
      *(ub32 *)loc |= bits(G, 9, 0);
      break;
    case R_SPARC_GOT13:
      *(ub32 *)loc |= bits(G, 12, 0);
      break;
    case R_SPARC_GOT22:
      *(ub32 *)loc |= bits(G >> 10, 21, 0);
      break;
    case R_SPARC_GOTDATA_HIX22:
    case R_SPARC_GOTDATA_OP_HIX22: {
      i64 val = S + A - GOT;
      *(ub32 *)loc |= bits((val >> 10) ^ (val >> 42), 21, 0);
      break;
    }
    case R_SPARC_GOTDATA_LOX10:
    case R_SPARC_GOTDATA_OP_LOX10: {
      i64 val = S + A - GOT;
      *(ub32 *)loc |= bits((val & 0x3ff) | (0x1c00 ^ ~((val >> 50) & 0x1c00)), 9, 0);
      break;
    }
    case R_SPARC_GOTDATA_OP:
      break;
    case R_SPARC_PC10:
    case R_SPARC_PCPLT10:
      *(ub32 *)loc |= bits(S + A - P, 9, 0);
      break;
    case R_SPARC_PC22:
    case R_SPARC_PCPLT22:
      *(ub32 *)loc |= bits((S + A - P) >> 10, 21, 0);
      break;
    case R_SPARC_OLO10:
      *(ub32 *)loc |= bits(S + A, 9, 0); // + O
      break;
    case R_SPARC_HH22:
      *(ub32 *)loc |= bits((S + A) >> 42, 21, 0);
      break;
    case R_SPARC_HM10:
      *(ub32 *)loc |= bits((S + A) >> 32, 9, 0);
      break;
    case R_SPARC_LM22:
      *(ub32 *)loc |= bits((S + A) >> 10, 21, 0);
      break;
    case R_SPARC_PC_HH22:
      *(ub32 *)loc |= bits((S + A - P) >> 42, 21, 0);
      break;
    case R_SPARC_PC_HM10:
      *(ub32 *)loc |= bits((S + A - P) >> 32, 9, 0);
      break;
    case R_SPARC_PC_LM22:
      *(ub32 *)loc |= bits((S + A - P) >> 10, 21, 0);
      break;
    case R_SPARC_WDISP16: {
      i64 val = (S + A - P) >> 2;
      *(ub16 *)loc |= (bit(val, 14) << 21) | bits(val, 13, 0);
      break;
    }
    case R_SPARC_WDISP19:
      *(ub32 *)loc |= bits((S + A - P) >> 2, 18, 0);
      break;
    case R_SPARC_DISP64:
      *(ub64 *)loc = S + A - P;
      break;
    case R_SPARC_PLT64:
      *(ub32 *)loc = S + A;
      break;
    case R_SPARC_HIX22:
      *(ub32 *)loc |= bits(~(S + A) >> 10, 21, 0);
      break;
    case R_SPARC_LOX10:
      *(ub32 *)loc |= bits(S + A, 9, 0) | 0b0001'1100'0000'0000;
      break;
    case R_SPARC_H44:
      *(ub32 *)loc |= bits((S + A) >> 22, 21, 0);
      break;
    case R_SPARC_M44:
      *(ub32 *)loc |= bits((S + A) >> 12, 9, 0);
      break;
    case R_SPARC_L44:
      *(ub32 *)loc |= bits(S + A, 11, 0);
      break;
    case R_SPARC_UA64:
    case R_SPARC_REGISTER:
      *(ub64 *)loc = S + A;
      break;
    default:
      Fatal(ctx) << *this << ": apply_reloc_alloc relocation: " << rel;
    }

#undef S
#undef A
#undef P
#undef G
#undef GOT
  }
}

template <>
void InputSection<E>::apply_reloc_nonalloc(Context<E> &ctx, u8 *base) {
  std::span<const ElfRel<E>> rels = get_rels(ctx);

  for (i64 i = 0; i < rels.size(); i++) {
    const ElfRel<E> &rel = rels[i];
    if (rel.r_type == R_NONE)
      continue;

    Symbol<E> &sym = *file.symbols[rel.r_sym];
    u8 *loc = base + rel.r_offset;

    if (!sym.file) {
      record_undef_error(ctx, rel);
      continue;
    }

    SectionFragment<E> *frag;
    i64 addend;
    std::tie(frag, addend) = get_fragment(ctx, rel);

    auto check = [&](i64 val, i64 lo, i64 hi) {
      if (val < lo || hi <= val)
        Error(ctx) << *this << ": relocation " << rel << " against "
                   << sym << " out of range: " << val << " is not in ["
                   << lo << ", " << hi << ")";
    };

#define S   (frag ? frag->get_addr(ctx) : sym.get_addr(ctx))
#define A   (frag ? addend : this->get_addend(rel))

    switch (rel.r_type) {
    case R_NONE:
      break;
    case R_SPARC_64:
      if (!frag) {
        if (std::optional<u64> val = get_tombstone(sym)) {
          *(ul64 *)loc = *val;
          break;
        }
      }
      *(ul64 *)loc = S + A;
      break;
    default:
      Fatal(ctx) << *this << ": apply_reloc_nonalloc: " << rel;
    }

#undef S
#undef A
  }
}

template <>
void InputSection<E>::scan_relocations(Context<E> &ctx) {
  assert(shdr().sh_flags & SHF_ALLOC);

  this->reldyn_offset = file.num_dynrel * sizeof(ElfRel<E>);
  std::span<const ElfRel<E>> rels = get_rels(ctx);

  // Scan relocations
  for (i64 i = 0; i < rels.size(); i++) {
    const ElfRel<E> &rel = rels[i];
    if (rel.r_type == R_NONE)
      continue;

    Symbol<E> &sym = *file.symbols[rel.r_sym];

    if (!sym.file) {
      record_undef_error(ctx, rel);
      continue;
    }

    if (sym.get_type() == STT_GNU_IFUNC)
      sym.flags |= (NEEDS_GOT | NEEDS_PLT);

    switch (rel.r_type) {
    case R_SPARC_8:
    case R_SPARC_10:
    case R_SPARC_11:
    case R_SPARC_13:
    case R_SPARC_16:
    case R_SPARC_22:
    case R_SPARC_32:
    case R_SPARC_64:
    case R_SPARC_REGISTER:
    case R_SPARC_UA16:
    case R_SPARC_UA32:
    case R_SPARC_UA64:
    case R_SPARC_PC_HM10:
    case R_SPARC_OLO10:
    case R_SPARC_LOX10:
    case R_SPARC_HM10:
    case R_SPARC_M44:
    case R_SPARC_HIX22:
    case R_SPARC_5:
    case R_SPARC_6:
    case R_SPARC_LO10:
    case R_SPARC_7:
    case R_SPARC_L44:
    case R_SPARC_LM22:
    case R_SPARC_HI22:
    case R_SPARC_H44:
    case R_SPARC_HH22:
      scan_abs_rel(ctx, sym, rel);
      break;
    case R_SPARC_PLT32:
    case R_SPARC_WPLT30:
    case R_SPARC_HIPLT22:
    case R_SPARC_LOPLT10:
    case R_SPARC_PCPLT32:
    case R_SPARC_PCPLT22:
    case R_SPARC_PCPLT10:
    case R_SPARC_PLT64:
      if (sym.is_imported)
        sym.flags |= NEEDS_PLT;
      break;
    case R_SPARC_GOT13:
    case R_SPARC_GOT10:
    case R_SPARC_GOT22:
    case R_SPARC_GOTDATA_HIX22:
    case R_SPARC_GOTDATA_LOX10:
    case R_SPARC_GOTDATA_OP_HIX22:
    case R_SPARC_GOTDATA_OP_LOX10:
    case R_SPARC_GOTDATA_OP:
      sym.flags |= NEEDS_GOT;
      break;
    case R_SPARC_DISP16:
    case R_SPARC_DISP32:
    case R_SPARC_DISP64:
    case R_SPARC_DISP8:
    case R_SPARC_PC10:
    case R_SPARC_PC22:
    case R_SPARC_PC_LM22:
    case R_SPARC_WDISP16:
    case R_SPARC_WDISP19:
    case R_SPARC_WDISP22:
    case R_SPARC_WDISP30:
    case R_SPARC_PC_HH22:
      scan_pcrel_rel(ctx, sym, rel);
      break;
    default:
      Fatal(ctx) << *this << ": scan_relocations: " << rel;
    }
  }
}

} // namespace mold::elf
