// METHODS
methods {
    // Authorizer
    function hasPermissions(address,address) external returns (bool) envfree;
    function hasPermission(address,address,bytes4) external returns (bool) envfree;
    function getPermissionsLength(address,address) external returns (uint256) envfree;
}

/*
    We want to count the authorized elements in the permissions mapping.  An authorized element is
    a key where the authorized field in the permissions structure is true, i.e., the key `what` where
    permissions[what] is allocated.
    We do this by introducing ghost that stores the authorized elements also in an array, more
    precisely, in a data structure that matches the EnumerableSet data structure of OpenZeppelin.

    The ghostPermissionsAuthorized mapping is a ghost copy of permissions.authorized.
    The ghostPermissionsLength mapping is the number of authorized permissions and also
    corresponds to permissions.count (we prove it in an invariant).
    The ghostPermissionsIndexes and ghsotPermissionsValues are the EnumerableSet view of all
    authorized permisssions.

        authorized: mapping(mathint => bool) for a copy of authorized field
        values: mapping(mathint => bytes4) for storing the key values of permissions mapping.
        indexes: mapping(bytes4 => mathint) for tracking the indexes in the values array.
        length: mathint to keep track of number of elements in the values mapping

    The set works as follows:
        indexes[value] = 0 : value is not in the set, authorized is false
        indexes[value] = x > 0 : values[x] == value, authorized is true

        i.e., the following holds

        for all values v . !authorized[v] => indexes[v] = 0
        for all values v . authorized[v] => indexes[v] in [1..length] && values[indexes[v]] = v
        for all indexes i. i in [1..length] => authorized[values[i]] && indexes[values[i]] = i

    Since in CVL we only have mappings, not arrays, we have to keep the length in a seperate ghost
    variable.  The values array is only defined for indexes in [1..length]. All other entries can be
    arbitrary. Note that we also do not use index 0 - this is reserved for indicating not allocated.

    Since we want the ghost working for every PermissionList, all theses ghost variables are really
    mapping from address `who` and address `where` to their respective types.
*/

// Ghosts for the Permissions set representation

// The initial size of the set is 0.
ghost mapping(address => mapping(address => mathint)) ghostPermissionsLength {
    init_state axiom forall address who. forall address where. ghostPermissionsLength[who][where] == 0;
}

// The initial state of values mapping shouldn't matter. We do not assume anything about the values since length = 0.
ghost mapping(address => mapping(address => mapping(mathint => bytes4))) ghostPermissionsValues;

// There is not element in the set, therefore, the mapping must send every "what" to 0.
ghost mapping(address => mapping(address => mapping(bytes4 => mathint))) ghostPermissionsIndexes {
    init_state axiom forall address who. forall address where. forall bytes4 what. ghostPermissionsIndexes[who][where][what] == 0;
}

// There is not element in the set, therefore, the mapping must be false for every "what".
ghost mapping(address => mapping(address => mapping(bytes4 => bool))) ghostAuthorized {
    init_state axiom forall address who. forall address where. forall bytes4 what. ghostAuthorized[who][where][what] == false;
}


// the basic invariants for our data structure.

definition hookValueInvariant(address who, address where, bytes4 what) returns bool =
    (!ghostAuthorized[who][where][what] => (
        ghostPermissionsIndexes[who][where][what] == 0
    ))
    && (ghostAuthorized[who][where][what] => (
        ghostPermissionsIndexes[who][where][what] > 0 &&
        ghostPermissionsIndexes[who][where][what] <= ghostPermissionsLength[who][where] &&
        ghostPermissionsValues[who][where][ghostPermissionsIndexes[who][where][what]] == what
    ));

definition hookIndexInvariant(address who, address where, mathint idx) returns bool =
    1 <= idx && idx <= ghostPermissionsLength[who][where] =>
       ghostPermissionsIndexes[who][where][ghostPermissionsValues[who][where][idx]] == idx &&
       ghostAuthorized[who][where][ghostPermissionsValues[who][where][idx]];

/*
    The ghostPermissionsAuthorized[who][where][what] field is always a copy of the contract's
    permissionLists[who][where].permissions[what].authorized field.

    This hook ensures that the ghost has the same list of permissions as the contract.  It
    uses the data structure described above to keep the permissions.

    The only require is that the ghost authorized field is always a copy of the contract's
    authorized field and this require always holds because of the assignment at the end of
    the hook.

    The ghost state update is verified to be correct by showing the invariants later.
*/
hook Sstore currentContract._permissionsLists[KEY address who][KEY address where].permissions[KEY bytes4 what].authorized bool newAuthorized (bool oldAuthorized) STORAGE {

    // ***************** //
    // **** REQUIRE **** //
    // ***************** //

    require ghostAuthorized[who][where][what] == oldAuthorized;

    // ***************** //
    // *** HOOK BODY *** //
    // ***************** //

    mathint length = ghostPermissionsLength[who][where];

    // Adding a permission
    if (newAuthorized && !oldAuthorized) {

        ghostPermissionsValues[who][where][length + 1] = what;  // 1 .. length are filled, length + 1 is free
        ghostPermissionsIndexes[who][where][what] = length + 1; // what is now on index length + 1
        ghostPermissionsLength[who][where] = length + 1;
    }

    // Deleting a permission
    if (!newAuthorized && oldAuthorized) {
        mathint indexOfWhat = ghostPermissionsIndexes[who][where][what];
        // Find the last value
        bytes4 lastValue = ghostPermissionsValues[who][where][length];
        // And put it where what was
        ghostPermissionsValues[who][where][indexOfWhat] = lastValue;
        ghostPermissionsIndexes[who][where][lastValue] = indexOfWhat;

        // Now "remove" what
        ghostPermissionsIndexes[who][where][what] = 0;
        ghostPermissionsLength[who][where] = length - 1;
    }

    ghostAuthorized[who][where][what] = newAuthorized;
}


// Make sure ghost and contract are the same when authorized is read
hook Sload bool authorized currentContract._permissionsLists[KEY address who][KEY address where].permissions[KEY bytes4 what].authorized STORAGE {
    require ghostAuthorized[who][where][what] == authorized;
}

/* show that the ghost invariants always hold */
invariant valueInvariant()
    forall address who. forall address where. forall bytes4 what.
        hookValueInvariant(who, where, what)
    {
        preserved {
            requireInvariant lengthInvariant();
            requireInvariant indexInvariant();
        }
    }

invariant indexInvariant()
    forall address who. forall address where. forall mathint idx.
        hookIndexInvariant(who, where, idx);

invariant lengthInvariant()
    forall address who. forall address where.
        ghostPermissionsLength[who][where] >= 0
    {
        preserved {
            requireInvariant valueInvariant();
        }
    }

// show that contract's permissionLists[who][where].count always corresponds to our ghost state.
invariant checkCount(address who, address where)
    ghostPermissionsLength[who][where] == to_mathint(getPermissionsLength(who, where));

// the target rule shows that hasPermission() implies hasPermissions() (i.e. length > 0).
rule hasPermissionsCorrect(address who, address where, bytes4 what)
{
    requireInvariant valueInvariant();
    requireInvariant checkCount(who, where);
    bool hasSinglePermission = hasPermission(who, where, what);

    assert hasSinglePermission => hasPermissions(who, where);
}
