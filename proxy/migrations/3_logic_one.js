var LogicOne = artifacts.require("./LogicOne.sol");

module.exports = function(deployer) {
  deployer.deploy(LogicOne);
  /**
  deployer.then(async () => {
    let s = await Storage.deployed();
    await deployer.deploy(LogicOne, s);
  })
  */
};
