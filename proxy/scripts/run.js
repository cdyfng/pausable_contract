const Registry = artifacts.require("Registry");
const LogicOne = artifacts.require("LogicOne");
const LogicTwo = artifacts.require("LogicTwo");

const dai_whale = "0x47ac0fb4f2d84898e4d9e7b4dab3c24507a6d503";

module.exports = async function (callback) {
  try {
    console.log("IT WORKS");
    let registry = await Registry.deployed();
    let logicOne = await LogicOne.deployed();
    let logicTwo = await LogicTwo.deployed();
    let r_address = await Registry.at(Registry.address);
    let r1 = await r_address.setLogicContract(LogicOne.address);
    console.log("r1: ", r1);
    let check_logic_contract = await r_address.logic_contract();
    console.log("check_logic_contract:", check_logic_contract);
    let l_one = await LogicOne.at(Registry.address);
    await l_one.setVal(2);
    let val = await l_one.val();
    console.log("val should be 4 :", val.toString());
    // check owner val
    let owner = await r_address.owner();
    console.log("owner :", owner);

    let r2 = await r_address.setLogicContract(LogicTwo.address);
    let l_two = await LogicTwo.at(Registry.address);
    await l_two.setVal(2);
    let val2 = await l_two.val();
    console.log("val should be 6 :", val2.toString());
  } catch (error) {
    console.log(error);
  }
  callback();
};
