#include "thumbsim.hpp"
// These are just the register NUMBERS
#define PC_REG 15  
#define LR_REG 14
#define SP_REG 13

// These are the contents of those registers
#define PC rf[PC_REG]
#define LR rf[LR_REG]
#define SP rf[SP_REG]

Stats stats;
Caches caches(0);

// CPE 315: you'll need to implement a custom sign-extension function
// in addition to the ones given below, specifically for the unconditional
// branch instruction, which has an 11-bit immediate field
unsigned int signExtend16to32ui(short i) {
  return static_cast<unsigned int>(static_cast<int>(i));
}

unsigned int signExtend8to32ui(char i) {
  return static_cast<unsigned int>(static_cast<int>(i));
}

// ADDED FOR UNCONDITIONAL BRANCH INSTRUCTION W 11-BIT IMMEDIATE FIELD
unsigned int signExtend11to32ui(char i) {
	return static_cast<unsigned int>(static_cast<int>(i));
}

// bitCount(): Counts number of ones in a bitstring, as
// specified on pg. 988 of ARMv7-M Reference Manual
unsigned int bitCount(unsigned short n) {
   unsigned int count = 0;
   while (n) {
      n = n & (n - 1);
      count++;
   }
   return count;
}


// This is the global object you'll use to store condition codes N,Z,V,C
// Set these bits appropriately in execute below.
ASPR flags;

// setNegativeZero(): It only takes one parameter as input, the 
// result of whatever operation is executing and it sets the "N"
// and "Z" flags
void setNegativeZero (int result) {
  if ((signed)result == 0) {
    flags.N = 0;
    flags.Z = 1;
  }
  else if ((signed)result < 0) {
    flags.N = 1;
    flags.Z = 0;
  }
  else {
    flags.N = 0;
    flags.Z = 0;
  }
}

// This function is complete, you should not have to modify it
void setCarryOverflow (int num1, int num2, OFType oftype) {
  switch (oftype) {
    case OF_ADD:
      if (((unsigned long long int)num1 + (unsigned long long int)num2) ==
          ((unsigned int)num1 + (unsigned int)num2)) {
        flags.C = 0;
      }
      else {
        flags.C = 1;
      }
      if (((long long int)num1 + (long long int)num2) ==
          ((int)num1 + (int)num2)) {
        flags.V = 0;
      }
      else {
        flags.V = 1;
      }
      break;
    case OF_SUB:
      if (num1 >= num2) {
        flags.C = 1;
      }
      else if (((unsigned long long int)num1 - (unsigned long long int)num2) ==
          ((unsigned int)num1 - (unsigned int)num2)) {
        flags.C = 0;
      }
      else {
        flags.C = 1;
      }
      if (((num1==0) && (num2==0)) ||
          (((long long int)num1 - (long long int)num2) ==
           ((int)num1 - (int)num2))) {
        flags.V = 0;
      }
      else {
        flags.V = 1;
      }
      break;
    case OF_SHIFT:
      // C flag unaffected for shifts by zero
      if (num2 != 0) {
        if (((unsigned long long int)num1 << (unsigned long long int)num2) ==
            ((unsigned int)num1 << (unsigned int)num2)) {
          flags.C = 0;
        }
        else {
          flags.C = 1;
        }
      }
      // Shift doesn't set overflow
      break;
    default:
      cerr << "Bad OverFlow Type encountered." << __LINE__ << __FILE__ << endl;
      exit(1);
  }
}

// CPE 315: You're given the code for evaluating BEQ, and you'll need to 
// complete the rest of these conditions. See Page 208 of the armv7 manual
static int checkCondition(unsigned short cond) {
  switch(cond) {
    case EQ:
      if (flags.Z == 1) {
        return TRUE;
      }
      break;
    case NE:
      if (flags.Z == 0) {
        return TRUE;
      }
      break;
    case CS:
      if (flags.C == 1) {
        return TRUE;
      }
      break;
    case CC:
      if (flags.C == 0) {
        return TRUE;
      }
      break;
    case MI:
      if (flags.N == 1) {
        return TRUE;
      }
      break;
    case PL:
      if (flags.N == 0) {
        return TRUE;
      }
      break;
    case VS:
      if (flags.V == 1) {
        return TRUE;
      }
      break;
    case VC:
      if (flags.V == 0) {
        return TRUE;
      }
      break;
    case HI:
      if (flags.C == 1 && flags.Z == 0) {
        return TRUE;
      }
      break;
    case LS:
      if (flags.C == 0 || flags.Z == 1) {
        return TRUE;
      }
      break;
    case GE:
      if (flags.N == flags.V) {
        return TRUE;
      }
      break;
    case LT:
      if (flags.N != flags.V) {
        return TRUE;
      }
      break;
    case GT:
      if (flags.Z == 0 && (flags.N == flags.V)) {
        return TRUE;
      }
      break;
    case LE:
      if (flags.Z == 1 || (flags.N != flags.V)) {
        return TRUE;
      }
      break;
    case AL:
      return TRUE;
      break;
  }
  return FALSE;
}

void execute() {
  Data16 instr = imem[PC];
  Data16 instr2;
  Data32 temp(0); // Use this for STRB instructions
  Thumb_Types itype;
  // the following counts as a read to PC
  unsigned int pctarget = PC + 2;
  unsigned int addr;
  int i, n, offset;
  unsigned int list, mask;
  int num1, num2, result, BitCount;
  unsigned int bit;

  /* Convert instruction to correct type */
  /* Types are described in Section A5 of the armv7 manual */
  BL_Type blupper(instr);
  ALU_Type alu(instr);
  SP_Type sp(instr);
  DP_Type dp(instr);
  LD_ST_Type ld_st(instr);
  MISC_Type misc(instr);
  COND_Type cond(instr);
  UNCOND_Type uncond(instr);
  LDM_Type ldm(instr);
  STM_Type stm(instr);
  LDRL_Type ldrl(instr);
  ADD_SP_Type addsp(instr);

  BL_Ops bl_ops;
  ALU_Ops add_ops;
  DP_Ops dp_ops;
  SP_Ops sp_ops;
  LD_ST_Ops ldst_ops;
  MISC_Ops misc_ops;

  // This counts as a write to the PC register
  rf.write(PC_REG, pctarget);

  itype = decode(ALL_Types(instr));

  // CPE 315: The bulk of your work is in the following switch statement
  // All instructions will need to have stats and cache access info added
  // as appropriate for that instruction.
  switch(itype) {
    case ALU:
      add_ops = decode(alu);
      switch(add_ops) {
        case ALU_LSLI:
          // part c: cache support
          result = rf[alu.instr.lsli.rm] << alu.instr.lsli.imm;
          rf.write(alu.instr.lsli.rd, result);
          setCarryOverflow(rf[alu.instr.lsli.rm], alu.instr.lsli.imm, OF_SHIFT);
          setNegativeZero((signed)result);
          // stats
          // - lsl <rd>, <rm>, #<imm5>
          // -     write,read
          stats.numRegReads++; 
          stats.numRegWrites++;
          stats.instrs++; 
          break;
        case ALU_ADDR:
          // part c: cache support
          rf.write(alu.instr.addr.rd, rf[alu.instr.addr.rn] + rf[alu.instr.addr.rm]);
          setCarryOverflow(rf[alu.instr.addr.rn], rf[alu.instr.addr.rm], OF_ADD);
          setNegativeZero((signed)rf[alu.instr.addr.rd]);
          // stats
          // - add <rd>, <rn>, <rm>
          // -     write,read,read
          stats.numRegReads+=2;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case ALU_SUBR:
          // part c: cache support
          rf.write(alu.instr.subr.rd, rf[alu.instr.subr.rn] - rf[alu.instr.subr.rm]);
          setCarryOverflow(rf[alu.instr.subr.rn], rf[alu.instr.subr.rm], OF_SUB);
          setNegativeZero((signed)rf[alu.instr.subr.rd]);
          // stats
          // - sub <rd>, <rn>, <rm>
          // -     write,read,read
          stats.numRegReads+=2;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case ALU_ADD3I:
          // part c: cache support
          rf.write(alu.instr.add3i.rd, rf[alu.instr.add3i.rn] + alu.instr.add3i.imm);
          setCarryOverflow(rf[alu.instr.add3i.rn], alu.instr.add3i.imm, OF_ADD);
          setNegativeZero((signed)rf[alu.instr.add3i.rd]);
          // stats
          // - add <rd>, <rn>, #<imm3>
          // -     write,read
          stats.numRegReads++;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case ALU_SUB3I:
          // part c: cache support
          rf.write(alu.instr.sub3i.rd, rf[alu.instr.sub3i.rn] - alu.instr.sub3i.imm);
          setCarryOverflow(rf[alu.instr.sub3i.rn], alu.instr.sub3i.imm, OF_SUB);
          setNegativeZero((signed)rf[alu.instr.sub3i.rd]);
          // stats
          // - add <rd>, <rn>, #<imm3>
          // -     write,read
          stats.numRegReads++;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case ALU_MOV:
          // part c: cache support
          rf.write(alu.instr.mov.rdn, alu.instr.mov.imm);
          setNegativeZero((signed)alu.instr.mov.imm);
          // stats
          // - mov <rd>, #<imm8>
          // -     write
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case ALU_CMP:
          // part c: cache support
          result = rf[alu.instr.cmp.rdn] - alu.instr.cmp.imm;
          setCarryOverflow(rf[alu.instr.cmp.rdn], alu.instr.cmp.imm, OF_SUB);
          setNegativeZero((signed)result);
          // stats
          // - cmp <rn>, #<imm8>
          // -     read
          stats.numRegReads++;
          stats.instrs++;
          break;
        case ALU_ADD8I:
          // part c: cache support
          rf.write(alu.instr.add8i.rdn, rf[alu.instr.add8i.rdn] + alu.instr.add8i.imm);
          setCarryOverflow(rf[alu.instr.add8i.rdn], alu.instr.add8i.imm, OF_ADD);
          setNegativeZero((signed)rf[alu.instr.add8i.rdn]);
          // stats
          // - add <rdn>, #<imm8>
          // -   read&write
          stats.numRegReads++;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case ALU_SUB8I:
          // part c: cache support
          rf.write(alu.instr.sub8i.rdn, rf[alu.instr.sub8i.rdn] - alu.instr.sub8i.imm);
          setCarryOverflow(rf[alu.instr.sub8i.rdn], alu.instr.sub8i.imm, OF_SUB);
          setNegativeZero((signed)rf[alu.instr.sub8i.rdn]);
          // stats
          // - sub <rdn>, #<imm8>
          // -   read&write
          stats.numRegReads++;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        default:
          cout << "instruction not implemented" << endl;
          exit(1);
          break;
      }
      break;
    case BL: 
      // PART B: BRANCH stats needed
      bl_ops = decode(blupper);
      if (bl_ops == BL_UPPER) {
        // PC has already been incremented above
        instr2 = imem[PC];
        BL_Type bllower(instr2);
        if (blupper.instr.bl_upper.s) {
          addr = static_cast<unsigned int>(0xff<<24) | 
            ((~(bllower.instr.bl_lower.j1 ^ blupper.instr.bl_upper.s))<<23) |
            ((~(bllower.instr.bl_lower.j2 ^ blupper.instr.bl_upper.s))<<22) |
            ((blupper.instr.bl_upper.imm10)<<12) |
            ((bllower.instr.bl_lower.imm11)<<1);
        }
        else {
          addr = ((blupper.instr.bl_upper.imm10)<<12) |
            ((bllower.instr.bl_lower.imm11)<<1);
        }
        // return address is 4-bytes away from the start of the BL insn
        rf.write(LR_REG, PC + 2);
          stats.numRegReads++;
        // Target address is also computed from that point
        rf.write(PC_REG, PC + 2 + addr);
          stats.numRegReads++;

        // stats
        stats.numBranches++;  // need to add stats for forward/backward branch ^^
        stats.numRegReads++;
        stats.numRegWrites+=2;
        stats.instrs++; 
      }
      else {
        cerr << "Bad BL format." << endl;
        exit(1);
      }
      break;
    case DP:
      dp_ops = decode(dp);
      switch(dp_ops) {
        case DP_CMP:
          // part c: cache support
          setCarryOverflow(rf[dp.instr.DP_Instr.rdn], rf[dp.instr.DP_Instr.rm], OF_SUB);
          setNegativeZero((signed)(rf[dp.instr.DP_Instr.rdn] - rf[dp.instr.DP_Instr.rm]));
          // stats
          // - cmp <rn>, <rm>
          // -     read,read
          stats.numRegReads+=2;
          stats.instrs++;
          break;
      }
      break;
    case SPECIAL:
      sp_ops = decode(sp);
      switch(sp_ops) {
        case SP_MOV:
          // part c: cache support
          rf.write((sp.instr.mov.d << 3) | sp.instr.mov.rd, rf[sp.instr.mov.rm]);
          setNegativeZero((signed)rf[sp.instr.mov.rm]);
          // stats
          // - mov <rd>, <rm>
          // -           read
          // - write => (sp.instr.mov.d << 3)
          stats.numRegReads++;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case SP_ADD:
          // part c: cache support
          result = rf[(sp.instr.add.d << 3) | sp.instr.add.rd] + rf[sp.instr.add.rm];
          rf.write((sp.instr.add.d << 3) | sp.instr.add.rd, result);
          setCarryOverflow(rf[(sp.instr.add.d << 3) | sp.instr.add.rd], rf[sp.instr.add.rm], OF_ADD);
          setNegativeZero((signed)result);
          // stats
          stats.numRegReads+=2;
          stats.numRegWrites++;
          stats.instrs++;
          break;
        case SP_CMP:
          // part c: cache support
          setCarryOverflow(rf[(sp.instr.cmp.d << 3) | sp.instr.cmp.rd], rf[sp.instr.cmp.rm], OF_SUB);
          setNegativeZero((signed)(rf[sp.instr.cmp.d < 3 | sp.instr.cmp.rd] - rf[sp.instr.cmp.rm]));
          // stats
          // - cmp <rn>, <rm>
          // -     read,read
          stats.numRegReads+=2;
          stats.instrs++;
          break;
      }
      break;
    case LD_ST:
      // You'll want to use these load and store models
      // to implement ldrb/strb, ldm/stm and push/pop
      ldst_ops = decode(ld_st);
      switch(ldst_ops) {
        case STRI:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_imm.rn] + ld_st.instr.ld_st_imm.imm * 4;
          dmem.write(addr, rf[ld_st.instr.ld_st_imm.rt]);
          // stats
          // str <rt>, [<rn>, #<imm5>]
          //     read, read&memory_write
          stats.numRegReads+=2;
          stats.numMemWrites++;
          stats.instrs++;
          break;
        case LDRI:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_imm.rn] + ld_st.instr.ld_st_imm.imm * 4;
          rf.write(ld_st.instr.ld_st_imm.rt, dmem[addr]);
          // stats
          // ldr <rt>, [<rn>, #<imm5>]
          //    write, memory_read
          stats.numRegWrites++;
          stats.numMemReads++;
          stats.instrs++;
          break;
        case STRR:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_reg.rn] + rf[ld_st.instr.ld_st_reg.rm];
          dmem.write(addr, rf[ld_st.instr.ld_st_reg.rt]);
          // stats
          // str <rt>, [<rn>, <rm>]
          //     read, read&read&memory_write
          stats.numRegReads+=3;
          stats.numMemWrites++;
          stats.instrs++;
          break;
        case LDRR:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_reg.rn] + rf[ld_st.instr.ld_st_reg.rm];
          rf.write(ld_st.instr.ld_st_reg.rt, dmem[addr]);
          // stats
          // ldr <rt>, [<rn>, <rm>]
          //    write, read&read&memory_read
          stats.numRegReads+=2;
          stats.numRegWrites++;
          stats.numMemReads++;
          stats.instrs++;
          break;
        case STRBI:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_imm.rn] + ld_st.instr.ld_st_imm.imm * 4;
          temp = dmem[addr];
          temp.set_data_ubyte4(0, rf[ld_st.instr.ld_st_imm.rt]);
          dmem.write(addr, temp);
          // stats
          // strb <rt>, [<rn>, #<imm5>]
          //      read, read&memory_write
          stats.numRegReads+=2;
          stats.numMemWrites++;
          stats.numMemReads++; // temp = dmem[addr] ^^
          stats.instrs++;
          break;
        case LDRBI:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_imm.rn] + ld_st.instr.ld_st_imm.imm * 4;
          temp = dmem[addr];
          rf.write(ld_st.instr.ld_st_imm.rt, temp.data_ubyte4(0));
          // stats
          // ldrb <rt>, [<rn>, #<imm5>]
          //     write, read&memory_read
          stats.numRegReads++;
          stats.numRegWrites++;
          stats.numMemReads++;
          stats.instrs++;
          break;
        case STRBR:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_reg.rn] + rf[ld_st.instr.ld_st_reg.rm];
          temp = dmem[addr];
          temp.set_data_ubyte4(0, rf[ld_st.instr.ld_st_reg.rt]);
          dmem.write(addr, temp);
          // stats
          // strb <rt>, [<rn>, <rm>]
          //      read, read&read&memory_write
          stats.numRegReads+=3;
          stats.numMemReads++; // temp = dmem[addr] ^^
          stats.numMemWrites++;
          stats.instrs++;
          break;
        case LDRBR:
          // part c: cache support
          addr = rf[ld_st.instr.ld_st_reg.rn] + rf[ld_st.instr.ld_st_reg.rm];
          temp = dmem[addr];
          rf.write(ld_st.instr.ld_st_reg.rt, temp.data_ubyte4(0));
          // stats
          // ldrb <rt>, [<rn>, <rm>]
          //     write, read&read&memory_read
          stats.numRegReads+=2;
          stats.numRegWrites++;
          stats.numMemReads+=2; // temp = dmem[addr] ^^
          stats.instrs++;
          break;
      }
      break;
    case MISC:
      misc_ops = decode(misc);
      switch(misc_ops) {
        case MISC_PUSH:
          // part c: cache support
          mask = 0x1;
          // pg. 390 of ARMv7-M Reference Manual
          BitCount = bitCount(misc.instr.push.reg_list) + misc.instr.push.m;
          addr = SP - 4 * BitCount;
            stats.numRegReads++;
          for (i=0; i<8; i++) {
            if (misc.instr.push.reg_list & mask) {
              dmem.write(addr, rf[i]);
              addr += 4;
              // stats: memory_write
              stats.numMemWrites++;
            }
            // update mask to next bit
            mask = mask << 1;
          }
          if (misc.instr.push.m == 1) {
            dmem.write(addr, LR);
              stats.numRegReads++;
            // stats: memory_write
            stats.numMemWrites++;
          }
          rf.write(SP_REG, SP - 4 * BitCount);
            stats.numRegReads++;
          // stats
          stats.numRegWrites++; // writing to SP_REG ^
          stats.instrs++;
          break;
        case MISC_POP:
          // needs stats
          mask = 0x1;
          BitCount = bitCount(misc.instr.pop.reg_list) + misc.instr.pop.m;
          addr = SP;
            stats.numRegReads++;
          for (i=0; i<8; i++) {
            if (misc.instr.pop.reg_list & mask) {
              rf.write(i, dmem[addr]);
              addr += 4;
              stats.numRegWrites++;
              stats.numMemReads++;
            }
            mask = mask << 1;
          }
          if (misc.instr.pop.m == 1) {
            rf.write(PC_REG, dmem[addr]);
            stats.numRegWrites++;
            stats.numMemReads++;
          }
          rf.write(SP_REG, SP + 4 * BitCount);
            stats.numRegReads++;
          // stats
          stats.numRegWrites++; // writing to SP_REG ^
          stats.instrs++;
          break;
        case MISC_SUB:
        // part c: cache support
          rf.write(SP_REG, SP - (misc.instr.sub.imm*4));
            stats.numRegReads++;
          setCarryOverflow(SP, misc.instr.sub.imm*4, OF_SUB);
          setNegativeZero(SP);
          // stats
          // sub sp, sp, #<imm7>
          stats.numRegWrites++; // writing to SP
          // SP is defined as rf[SP_REG]
          stats.instrs++;
          break;
        case MISC_ADD:
          // part c: cache support
          rf.write(SP_REG, SP + (misc.instr.add.imm*4));
            // SP read
            stats.numRegReads++;
          setCarryOverflow(SP, misc.instr.add.imm*4, OF_ADD);
          setNegativeZero(SP);
          // stats
          // add sp, sp, #<imm7>
          stats.numRegWrites++;
          stats.instrs++;
          break;
      }
      break;
    case COND:
      decode(cond);
      // part c: cache support
      if (checkCondition(cond.instr.b.cond)){
        rf.write(PC_REG, PC + 2 * signExtend8to32ui(cond.instr.b.imm) + 2);
        // PC read
        stats.numRegReads++;
        stats.numRegWrites++;
        stats.numBranches++;
        // stats.numForwardBranchesTaken++;
        // ^ commented out bc I'm not sure if this is a "forward branch" but some
        // branch stat defintely needs to be incremented here
      }
      // incrementing instructions stat, may not be necessary
      stats.instrs++;
      break;
    case UNCOND:
      // part c: cache support
      decode(uncond);
      rf.write(PC_REG, PC + 2 * signExtend11to32ui(cond.instr.b.imm) + 2);
      // PC read
      stats.numRegReads++;
      // stats
      // b <label>
      stats.numRegWrites++;
      stats.numBranches++;
      stats.instrs++;
      break;
    case LDM:
      // part c: cache support
      decode(ldm);
      mask = 0x1;
      BitCount = bitCount(ldm.instr.ldm.reg_list);
      addr = rf[ldm.instr.ldm.rn];
      for (i=0; i<8; i++) {
        if (ldm.instr.ldm.reg_list & mask) {
          rf.write(i, dmem[addr]);
          addr += 4;
          // stats: memory_read & register_write
          stats.numRegWrites++;
          stats.numMemReads++;
        }
        mask = mask << 1;
      }
      rf.write(ldm.instr.ldm.rn, rf[ldm.instr.ldm.rn] + 4 * BitCount);
      // stats
      // ldm <rn>!, <register>
      //     read, reading from these registers
      stats.numRegReads++;
      stats.numRegWrites++;
      stats.instrs++;
      break;
    case STM:
      // part c: cache support
      decode(stm);
      mask = 0x1;
      BitCount = bitCount(stm.instr.stm.reg_list);
      addr = rf[stm.instr.stm.rn];
      for (i=0; i<8; i++) {
        if (stm.instr.stm.reg_list & mask) {
          dmem.write(addr, rf[i]);
          addr += 4;
          // stats: memory_write & register_read
          stats.numRegReads++;
          stats.numMemWrites++;
        }
        mask = mask << 1;
      }
      rf.write(stm.instr.stm.rn, rf[stm.instr.stm.rn] + 4 * BitCount);
      // stats
      // stm <rn>!, <register>
      //     read, writing to these registers
      stats.numRegReads++;
      stats.numRegWrites++;
      stats.instrs++;
      break;
    case LDRL:
      // complete
      decode(ldrl);
      // Need to check for alignment by 4
      if (PC & 2) {
        addr = PC + 2 + (ldrl.instr.ldrl.imm)*4;
      }
      else {
        addr = PC + (ldrl.instr.ldrl.imm)*4;
      }
      // Requires two consecutive imem locations pieced together
      temp = imem[addr] | (imem[addr+2]<<16);  // temp is a Data32
      rf.write(ldrl.instr.ldrl.rt, temp);

      // One write for updated reg
      stats.numRegWrites++;
      // One read of the PC
      // SO HERE USING 'PC' AS A VARIABLE COUNTED AS READING A REGISTER SO I DID THE SAME W 'SP'
      stats.numRegReads++;
      // One mem read, even though it's imem, and there's two of them
      stats.numMemReads++;
      stats.instrs++;
      break;
    case ADD_SP:
      // part c: cache support
      decode(addsp);
      rf.write(addsp.instr.add.rd, SP + (addsp.instr.add.imm*4));
      // stats
      // add <rd>, sp, #<imm8>
      //    write
      stats.numRegWrites++;
      // SP is a register read defined above
      stats.numRegReads++;
      stats.instrs++;
      break;
    default:
      cout << "[ERROR] Unknown Instruction to be executed" << endl;
      exit(1);
      break;
  }
}
