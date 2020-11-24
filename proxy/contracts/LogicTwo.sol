pragma solidity 0.5.16;
import './LogicOne.sol';

contract LogicTwo is LogicOne {
    function setVal(uint _val) public returns (bool success) {
        val = 3 * _val;
        return true;
    }
}
