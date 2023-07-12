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

// - signExtend11Bit func
// - SP_ADD
// - SP_CMP
// - STRBI
// - LDRBI
// - STRBR
// - LDRBR 
// - LDM
// - STM


// class Stats {
//    public:
//       unsigned int instrs;
//       unsigned int cycles;

//       unsigned int numMemWrites;
//       unsigned int numMemReads;
//       unsigned int numBranches;
//       unsigned int numRegWrites;
//       unsigned int numRegReads;

//       unsigned int numForwardBranchesTaken;
//       unsigned int numForwardBranchesNotTaken;
//       unsigned int numBackwardBranchesTaken;
//       unsigned int numBackwardBranchesNotTaken;



// CPE 315: you'll need to implement a custom sign-extension function
// in addition to the ones given below, specifically for the unconditional
// branch instruction, which has an 11-bit immediate field
unsigned int signExtend11to32ui(short i) {
  if (i  >> 10 & 1) {
    return static_cast<unsigned int>(static_cast<int>(i & 0b1111111111111111));
  }
  else {
    return static_cast<unsigned int>(static_cast<int>(i & 0b0000011111111111));
  }
}

unsigned int signExtend16to32ui(short i) {
  return static_cast<unsigned int>(static_cast<int>(i));
}

unsigned int signExtend8to32ui(char i) {
  return static_cast<unsigned int>(static_cast<int>(i));
}

// This is the global object you'll use to store condition codes N,Z,V,C
// Set these bits appropriately in execute below.
ASPR flags;

// CPE 315: You need to implement a function to set the Negative and Zero
// flags for each instruction that does that. It only needs to take
// one parameter as input, the result of whatever operation is executing
void setNegativeZero(int result){
  if ((signed)result < 0){
    flags.N = 1;
  }
  else{
    flags.N = 0;
  }
  if((signed)result == 0){
    flags.Z = 1;
  }
  else{
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

//return regs set
unsigned int getBitCount(unsigned short i){
  unsigned int cnt;
  while (i){
    i = i & (i - 1);
    cnt = cnt + 1;
  }
  return cnt;
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
  unsigned short registers = 0;
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
          stats.instrs++;
          result = rf[alu.instr.lsli.rm] << alu.instr.lsli.imm;
          rf.write(alu.instr.lsli.rd, result);
          setNegativeZero(result);
          setCarryOverflow(rf[alu.instr.lsli.rm], alu.instr.lsli.imm, OF_SHIFT);
          break;
        case ALU_ADDR:
          stats.instrs++;
          // needs stats and flags
          result = rf[alu.instr.addr.rn] + rf[alu.instr.addr.rm];
          rf.write(alu.instr.addr.rd, result);
          setNegativeZero((signed)rf[alu.instr.addr.rd]);
          setCarryOverflow(rf[alu.instr.addr.rn], rf[alu.instr.addr.rm], OF_ADD);
          break;
          
        case ALU_SUBR:
          stats.instrs++;
          result = rf[alu.instr.subr.rn] - rf[alu.instr.subr.rm];
          rf.write(alu.instr.subr.rd, result);
          setNegativeZero((signed)rf[alu.instr.subr.rd]);
          setCarryOverflow(rf[alu.instr.subr.rn], rf[alu.instr.subr.rm], OF_SUB);
          break;
        case ALU_ADD3I:
          stats.instrs++;
          // needs stats and flags
          result = rf[alu.instr.add3i.rn] + alu.instr.add3i.imm;
          rf.write(alu.instr.add3i.rd, result);
          setNegativeZero(result);
          setCarryOverflow(rf[alu.instr.add3i.rn], alu.instr.add3i.imm, OF_ADD);
          break;
        case ALU_SUB3I:
          stats.instrs++;
          result = rf[alu.instr.sub3i.rn] - alu.instr.sub3i.imm;
          rf.write(alu.instr.sub3i.rd, result);
          setNegativeZero(result);
          setCarryOverflow(rf[alu.instr.sub3i.rn], alu.instr.sub3i.imm, OF_SUB);
          break;
        case ALU_MOV:
          stats.instrs++;
          // needs stats and flags
          rf.write(alu.instr.mov.rdn, alu.instr.mov.imm);
          break;
        case ALU_CMP:
          stats.instrs++;
          setNegativeZero(rf[alu.instr.cmp.rdn] - alu.instr.cmp.imm);
          setCarryOverflow(rf[alu.instr.cmp.rdn], alu.instr.cmp.imm, OF_SUB);
          break;
        case ALU_ADD8I:
          stats.instrs++;
          // needs stats and flags
          result = rf[alu.instr.add8i.rdn] + alu.instr.add8i.imm;
          rf.write(alu.instr.add8i.rdn, result);
          setNegativeZero(result);
          setCarryOverflow(rf[alu.instr.add8i.rdn], alu.instr.add8i.imm, OF_ADD);
          break;
        case ALU_SUB8I:
          stats.instrs++;
          result = rf[alu.instr.sub8i.rdn] - alu.instr.sub8i.imm;
          rf.write(alu.instr.sub8i.rdn, result);
          setNegativeZero(result);
          setCarryOverflow(rf[alu.instr.sub8i.rdn], alu.instr.sub8i.imm, OF_SUB);
          break;
        default:
          cout << "instruction not implemented" << endl;
          exit(1);
          break;
      }
      break;
    case BL: 
      stats.instrs++;
      // This instruction is complete, nothing needed here
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
        // Target address is also computed from that point
        rf.write(PC_REG, PC + 2 + addr);

        stats.numRegReads += 1;
        stats.numRegWrites += 2; 
      }
      else {
        cerr << "Bad BL format." << endl;
        exit(1);
      }
      break;
    case DP:
      stats.instrs++;
      dp_ops = decode(dp);
      switch(dp_ops) {
        case DP_CMP:
          // need to implement
          result = rf[dp.instr.DP_Instr.rdn] - rf[dp.instr.DP_Instr.rm];
          setNegativeZero(result);
          setCarryOverflow(rf[dp.instr.DP_Instr.rdn], rf[dp.instr.DP_Instr.rm], OF_SUB);
          break;
      }
      break;
    case SPECIAL:
      sp_ops = decode(sp);
      switch(sp_ops) {
        case SP_MOV:
          stats.instrs++;
          // needs stats and flags
          rf.write((sp.instr.mov.d << 3 ) | sp.instr.mov.rd, rf[sp.instr.mov.rm]);
          break;
        case SP_ADD:
          stats.instrs++;
          // Special SP cases do not update the flags
          if (sp.instr.add.rm == 13) { // special case: ADD (SP + reg)
          rf.write((sp.instr.add.d << 3) | sp.instr.add.rd, SP + rf[(sp.instr.add.d << 3) | sp.instr.add.rd]);

          stats.numRegReads += 2;
          stats.numRegWrites += 1;
          }
          else if (sp.instr.add.d == 1 && sp.instr.add.rd == 5) { // special case: ADD (SP + reg)
          rf.write(SP_REG, SP + rf[sp.instr.add.rm]);

          stats.numRegReads += 2;
          stats.numRegWrites += 1;
          }
          else { // regular case
          setCarryOverflow(rf[sp.instr.add.rm], rf[(sp.instr.add.d << 3) | sp.instr.add.rd], OF_ADD);
          setNegativeZero(rf[sp.instr.add.rm] + rf[(sp.instr.add.d << 3) | sp.instr.add.rd]);
          rf.write((sp.instr.add.d << 3) | sp.instr.add.rd, rf[sp.instr.add.rm] + rf[(sp.instr.add.d << 3) | sp.instr.add.rd]);

          stats.numRegReads += 2;
          stats.numRegWrites += 1;
          }
          break;
        case SP_CMP: 
          stats.instrs++;
          // need to implement thes
          break;
      }
      break;
    case LD_ST:
      // You'll want to use these load and store models
      // to implement ldrb/strb, ldm/stm and push/pop
      ldst_ops = decode(ld_st);
      switch(ldst_ops) {

        case STRI:
          // functionally complete, needs statsS
          stats.instrs++;
          addr = rf[ld_st.instr.ld_st_imm.rn] + (ld_st.instr.ld_st_imm.imm * 4);
          stats.numMemWrites++;
          dmem.write(addr, rf[ld_st.instr.ld_st_imm.rt]);
          caches.access(addr);
          break;
        case LDRI:
          stats.instrs++;
          // functionally complete, needs stats
          addr = rf[ld_st.instr.ld_st_imm.rn] + (ld_st.instr.ld_st_imm.imm * 4);
          stats.numMemReads++;
          rf.write(ld_st.instr.ld_st_imm.rt, dmem[addr]);
          caches.access(addr);
          break;
        case STRR:
          stats.instrs++;
          // need to implement
          addr = rf[ld_st.instr.ld_st_reg.rn] + (rf[ld_st.instr.ld_st_reg.rm]);
          stats.numMemWrites++;
          dmem.write(addr, rf[ld_st.instr.ld_st_reg.rt]);
          caches.access(addr);
          break;
        case LDRR:
          stats.instrs++;
          // need to implement
          addr = rf[ld_st.instr.ld_st_reg.rn] + (rf[ld_st.instr.ld_st_reg.rm]);
          rf.write(ld_st.instr.ld_st_reg.rt, dmem[addr]);
          caches.access(addr);
          stats.numMemReads++;
          break;
        case STRBI:
          stats.instrs++;
          // need to implement
          addr = rf[ld_st.instr.ld_st_imm.rn] + (ld_st.instr.ld_st_imm.imm);
          stats.numMemWrites++;
          dmem.write(addr, static_cast<char>(rf[ld_st.instr.ld_st_imm.rt]));
          caches.access(addr);
          break;
        case LDRBI:
          stats.instrs++;
          addr = rf[ld_st.instr.ld_st_imm.rn] + (ld_st.instr.ld_st_imm.imm);
          rf.write(ld_st.instr.ld_st_imm.rt, static_cast<char>(dmem[addr]));
          caches.access(addr);
          stats.numMemReads++;
          break;
          // need to implement
          
        case STRBR:
          stats.instrs++;
          // need to implement
          addr = rf[ld_st.instr.ld_st_reg.rn] + (rf[ld_st.instr.ld_st_reg.rm]);
          stats.numMemWrites++;
          dmem.write(addr, static_cast<char>(rf[ld_st.instr.ld_st_imm.rt]));
          caches.access(addr);
          break;
      
        case LDRBR:
          stats.instrs++;
          // need to implement
          addr = rf[ld_st.instr.ld_st_reg.rn] + (rf[ld_st.instr.ld_st_reg.rm]);
          rf.write(ld_st.instr.ld_st_reg.rt, static_cast<char>(dmem[addr]));
          caches.access(addr);
          stats.numMemReads++;
          break;
      }
      break;
    case MISC:
      misc_ops = decode(misc);
      switch(misc_ops) {
        case MISC_PUSH:
          stats.instrs++;
          // need to implement
          BitCount = getBitCount(misc.instr.push.reg_list) + misc.instr.push.m;
          addr = SP - 4 * BitCount;

          for (int i = 0; i < 8; i++)
          {
            if (((int)pow(2, i)) & misc.instr.push.reg_list) {
              dmem.write(addr, rf[i]);
              caches.access(addr);
              stats.numMemWrites++;
              addr = addr + 4;
            }
          }
          if (misc.instr.push.m == 1) {
            dmem.write(addr, LR);
            caches.access(addr);
            stats.numMemWrites++;
          }
          rf.write(SP_REG, SP - 4 * BitCount);

          break;
        case MISC_POP:
          stats.instrs++;
          addr = SP;
          registers = (misc.instr.pop.m << 15) | misc.instr.pop.reg_list;
          BitCount = getBitCount(misc.instr.pop.reg_list);
          for(int i = 0; i < 15; i++){
            if(((int)pow(2, i)) & registers) {
              rf.write(i, dmem[addr]);
              caches.access(addr);
              stats.numMemReads++;
              addr+=4;
            }
          }
          if(((int)pow(2, 15)) & registers) {
              rf.write(PC_REG, dmem[addr]);
              caches.access(addr);
              stats.numMemReads++;
          }
          rf.write(SP_REG, SP + 4*BitCount);
          break;
        case MISC_SUB:
          stats.instrs++;
          // functionally complete, needs stats
          rf.write(SP_REG, SP - (misc.instr.sub.imm*4));
          break;
        case MISC_ADD:
          stats.instrs++;
          // functionally complete, needs stats
          rf.write(SP_REG, SP + (misc.instr.add.imm*4));
          break;
      }
      break;
    case COND:
      decode(cond);
      stats.instrs++;
      // Once you've completed the checkCondition function,
      // this should work for all your conditional branches.
      // needs stats   
        if (checkCondition(cond.instr.b.cond)){
          rf.write(PC_REG, PC + 2 * signExtend8to32ui(cond.instr.b.imm) + 2);
          if(PC + (2 * signExtend8to32ui(cond.instr.b.imm)) <= PC){
            stats.numBranches++;   
            stats.numBackwardBranchesTaken++;
          }
          else{
            stats.numBranches++;   
            stats.numForwardBranchesTaken++;
          }
        }
        else{
          if(PC + (2 * signExtend8to32ui(cond.instr.b.imm)) <= PC){
            stats.numBackwardBranchesNotTaken++;
          }
          else{
            stats.numForwardBranchesNotTaken++;
          }
        }    
      break;
    case UNCOND:
      // Essentially the same as the conditional branches, but with no
      // condition check, and an 11-bit immediate field
      decode(uncond);
      rf.write(PC_REG, PC + 2 * signExtend11to32ui(cond.instr.b.imm) + 2);
      stats.instrs++;
      break;
    case LDM:
      decode(ldm);
      // need to implement
      stats.instrs++;
      break;
    case STM:
      decode(stm);
      //for i = 0 to 14
        //if registers<i> == ‘1’ then
          //if i == n && wback && i != LowestSetBit(registers) then
            //MemA[address,4] = bits(32) UNKNOWN; // encoding T1 only
          //else
            //MemA[address,4] = R[i];
          //address = address + 4;
      // need to implement
      stats.instrs++;
      break;
    case LDRL:
      // This instruction is complete, nothing needed
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
      stats.numRegReads++;
      // One mem read, even though it's imem, and there's two of them
      stats.numMemReads++;
      stats.instrs++;
      break;
    case ADD_SP:
      // needs stats
      decode(addsp);
      stats.instrs++;
      rf.write(addsp.instr.add.rd, SP + (addsp.instr.add.imm*4));
      break;
    default:
      cout << "[ERROR] Unknown Instruction to be executed" << endl;
      exit(1);
      break;
  }
}
