// SPDX-License-Identifier: GPL-3.0-or-later
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

pragma solidity >=0.8.0;

import '../ITask.sol';

/**
 * @dev Base bridge task interface
 */
interface IBaseBridgeTask is ITask {
    /**
     * @dev The token is zero
     */
    error TaskTokenZero();

    /**
     * @dev The amount is zero
     */
    error TaskAmountZero();

    /**
     * @dev The recipient is zero
     */
    error TaskRecipientZero();

    /**
     * @dev The connector is zero
     */
    error TaskConnectorZero();

    /**
     * @dev The next balance connector is not zero
     */
    error TaskNextConnectorNotZero(bytes32 id);

    /**
     * @dev The destination chain is not set
     */
    error TaskDestinationChainNotSet();

    /**
     * @dev The destination chain id is the same as the current chain id
     */
    error TaskBridgeCurrentChainId(uint256 destinationChain);

    /**
     * @dev The slippage to be set is greater than one
     */
    error TaskSlippageAboveOne();

    /**
     * @dev The requested slippage is greater than the maximum slippage
     */
    error TaskSlippageAboveMax(uint256 slippage, uint256 maxSlippage);

    /**
     * @dev The requested fee percentage is greater than the maximum fee percentage
     */
    error TaskFeePctAboveMax(uint256 feePct, uint256 maxFeePct);

    /**
     * @dev Emitted every time the connector is set
     */
    event ConnectorSet(address indexed connector);

    /**
     * @dev Emitted every time the recipient is set
     */
    event RecipientSet(address indexed recipient);

    /**
     * @dev Emitted every time the default destination chain is set
     */
    event DefaultDestinationChainSet(uint256 indexed defaultDestinationChain);

    /**
     * @dev Emitted every time the default max slippage is set
     */
    event DefaultMaxSlippageSet(uint256 maxSlippage);

    /**
     * @dev Emitted every time a custom destination chain is set for a token
     */
    event CustomDestinationChainSet(address indexed token, uint256 indexed destinationChain);

    /**
     * @dev Emitted every time a custom max slippage is set
     */
    event CustomMaxSlippageSet(address indexed token, uint256 maxSlippage);

    /**
     * @dev Tells the connector tied to the task
     */
    function connector() external view returns (address);

    /**
     * @dev Tells the address of the allowed recipient
     */
    function recipient() external view returns (address);

    /**
     * @dev Tells the default destination chain
     */
    function defaultDestinationChain() external view returns (uint256);

    /**
     * @dev Tells the default max slippage
     */
    function defaultMaxSlippage() external view returns (uint256);

    /**
     * @dev Tells the destination chain defined for a specific token
     * @param token Address of the token being queried
     */
    function customDestinationChain(address token) external view returns (uint256);

    /**
     * @dev Tells the max slippage defined for a specific token
     * @param token Address of the token being queried
     */
    function customMaxSlippage(address token) external view returns (uint256);

    /**
     * @dev Tells the destination chain that should be used for a token
     * @param token Address of the token to get the destination chain for
     */
    function getDestinationChain(address token) external view returns (uint256);

    /**
     * @dev Tells the max slippage that should be used for a token
     * @param token Address of the token to get the max slippage for
     */
    function getMaxSlippage(address token) external view returns (uint256);

    /**
     * @dev Sets a new connector
     * @param newConnector Address of the connector to be set
     */
    function setConnector(address newConnector) external;

    /**
     * @dev Sets the recipient address
     * @param recipient Address of the new recipient to be set
     */
    function setRecipient(address recipient) external;

    /**
     * @dev Sets the default destination chain
     * @param destinationChain Default destination chain to be set
     */
    function setDefaultDestinationChain(uint256 destinationChain) external;

    /**
     * @dev Sets the default max slippage
     * @param maxSlippage Default max slippage to be set
     */
    function setDefaultMaxSlippage(uint256 maxSlippage) external;

    /**
     * @dev Sets a custom destination chain for a token
     * @param token Address of the token to set a custom destination chain for
     * @param destinationChain Destination chain to be set
     */
    function setCustomDestinationChain(address token, uint256 destinationChain) external;

    /**
     * @dev Sets a custom max slippage
     * @param token Address of the token to set a custom max slippage for
     * @param maxSlippage Max slippage to be set
     */
    function setCustomMaxSlippage(address token, uint256 maxSlippage) external;
}
