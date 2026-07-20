// ==========================================
// Global Variables & Configuration
// ==========================================
let map;
let dataLayers = [];
let isMeasuring = false;
const searchMarkers = [];
const CONFIG = {
    startCoords: [-15.80337498, 35.0385198],
    startZoom: 15.5,
    maxZoom: 22,
    // Seven decimal places is about 1 cm. It joins GIS junctions that differ only
    // by floating-point noise without joining genuinely separate roads.
    networkNodePrecision: 7,
    utm36S: "+proj=utm +zone=36 +south +datum=WGS84 +units=m +no_defs",
    malawiBounds: { latMin: -18.0, latMax: -9.0, lonMin: 32.0, lonMax: 36.5 },
    styles: {
        boundary: { color: "red", weight: 5, fillOpacity: 0 },
        postcode: { color: "red", weight: 0, fillOpacity: 0, stroke: false },
        nas: { color: "black", weight: 1, fillOpacity: 0 },
        road: { color: "#999", weight: 3, fillOpacity: 0.08 },
        highlight: { color: "#ffff00", weight: 5, stroke: true },
        route: {
            color: "#3458EB",
            weight: 8,
            opacity: 0.85,
            lineCap: "round",
            lineJoin: "round",
        },
        connector: {
            color: "#00b5d0",
            weight: 4,
            opacity: 0.9,
            dashArray: "7 7",
            lineCap: "round",
        },
    },
    wgs84Regex: /^([-+]?\d{1,3}(?:\.\d+)?),\s*([-+]?\d{1,3}(?:\.\d+)?)$/,
    utmRegex: /^(\d{6,7}(?:\.\d+)?),\s*(\d{6,7}(?:\.\d+)?)$/,
};
// Each graph edge has the road metadata needed to build directions.
let networkGraph = {};
let networkComponentByNode = {};
let nasAddressIndex = [];
const routingState = {
    activeMode: null,
    startNodeKey: null,
    endNodeKey: null,
    startActualLatLng: null, // Exact user / NAS coordinate. Never moved onto a road.
    endActualLatLng: null,
    startMarker: null,
    endMarker: null,
    startConnector: null,
    endConnector: null,
    routeLine: null,
};

// ==========================================
// General Utility Functions
// ==========================================
function clearSearchMarkers() {
    searchMarkers.forEach((marker) => {
        if (map && map.hasLayer(marker)) map.removeLayer(marker);
    });
    searchMarkers.length = 0;
}
function debounce(fn, delay) {
    let timeout;
    return function (...args) {
        clearTimeout(timeout);
        timeout = setTimeout(() => fn(...args), delay);
    };
}
function escapeHtml(value) {
    return String(value == null ? "" : value)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#039;");
}
function createPopup(title, data) {
    const properties = Object.entries(data)
        .map(
            ([label, value]) =>
                "<b>" +
                escapeHtml(label) +
                ":</b> " +
                escapeHtml(value || "N/A")
        )
        .join("<br>");
    return "<h3>" + escapeHtml(title) + "</h3><p>" + properties + "</p>";
}
function getPointCoordinate(feature) {
    if (!feature || !feature.geometry) return null;
    const geometry = feature.geometry;
    if (geometry.type === "Point" && Array.isArray(geometry.coordinates))
        return geometry.coordinates;
    if (
        geometry.type === "MultiPoint" &&
        Array.isArray(geometry.coordinates) &&
        geometry.coordinates.length
    ) {
        return geometry.coordinates[0];
    }
    return null;
}
// NAS data is sometimes delivered as address polygons or lines rather than points.
// Use Turf to get a valid map coordinate for every GeoJSON geometry type.
function getAddressCoordinate(feature) {
    const directPoint = getPointCoordinate(feature);
    if (directPoint) return directPoint;
    if (
        !feature ||
        !feature.geometry ||
        !Array.isArray(feature.geometry.coordinates)
    )
        return null;
    function firstValidCoordinate(coordinates) {
        if (!Array.isArray(coordinates)) return null;
        if (
            coordinates.length >= 2 &&
            !Array.isArray(coordinates[0]) &&
            !Array.isArray(coordinates[1])
        ) {
            const longitude = Number(coordinates[0]);
            const latitude = Number(coordinates[1]);
            return Number.isFinite(longitude) && Number.isFinite(latitude)
                ? [longitude, latitude]
                : null;
        }
        for (const child of coordinates) {
            const coordinate = firstValidCoordinate(child);
            if (coordinate) return coordinate;
        }
        return null;
    }
    function normaliseCoordinateTree(coordinates) {
        if (Array.isArray(coordinates))
            return coordinates.map(normaliseCoordinateTree);
        if (typeof coordinates === "string" && coordinates.trim() !== "")
            return Number(coordinates);
        return coordinates;
    }
    function allPositionsAreFinite(coordinates) {
        if (!Array.isArray(coordinates)) return false;
        if (
            coordinates.length >= 2 &&
            !Array.isArray(coordinates[0]) &&
            !Array.isArray(coordinates[1])
        ) {
            return (
                Number.isFinite(coordinates[0]) &&
                Number.isFinite(coordinates[1])
            );
        }
        return (
            coordinates.length > 0 && coordinates.every(allPositionsAreFinite)
        );
    }
    const fallbackCoordinate = firstValidCoordinate(
        feature.geometry.coordinates
    );
    if (!fallbackCoordinate) return null; // This feature has no valid map coordinate.
    const normalisedCoordinates = normaliseCoordinateTree(
        feature.geometry.coordinates
    );
    if (
        allPositionsAreFinite(normalisedCoordinates) &&
        typeof turf !== "undefined" &&
        turf.pointOnFeature
    ) {
        try {
            const normalisedFeature = Object.assign({}, feature, {
                geometry: Object.assign({}, feature.geometry, {
                    coordinates: normalisedCoordinates,
                }),
            });
            const point = turf.pointOnFeature(normalisedFeature);
            if (
                point &&
                point.geometry &&
                Array.isArray(point.geometry.coordinates)
            ) {
                return point.geometry.coordinates;
            }
        } catch (error) {
            // A malformed polygon must not prevent the rest of the NAS layer from being searchable.
        }
    }
    // Invalid polygons/lines still produce a useful search result at their first valid vertex.
    return fallbackCoordinate;
}
function getNasProperty(properties, candidates) {
    if (!properties) return "";
    const normalise = (value) =>
        String(value)
            .toLowerCase()
            .replace(/[^a-z0-9]/g, "");
    const propertyByName = {};
    Object.keys(properties).forEach((key) => {
        propertyByName[normalise(key)] = properties[key];
    });
    for (const candidate of candidates) {
        const value = propertyByName[normalise(candidate)];
        if (
            value !== undefined &&
            value !== null &&
            String(value).trim() !== ""
        )
            return value;
    }
    return "";
}
function formatDistance(kilometres) {
    if (!Number.isFinite(kilometres)) return "0 m";
    return kilometres < 1
        ? Math.round(kilometres * 1000) + " m"
        : kilometres.toFixed(kilometres < 10 ? 2 : 1) + " km";
}
function formatDuration(hours) {
    const totalMinutes = Math.max(1, Math.round(hours * 60));
    if (totalMinutes < 60) return totalMinutes + " min";
    const hoursPart = Math.floor(totalMinutes / 60);
    const minutesPart = totalMinutes % 60;
    return hoursPart + " h" + (minutesPart ? " " + minutesPart + " min" : "");
}
function getNodeLatLng(nodeKey) {
    const coords = nodeKey.split(",").map(Number);
    return L.latLng(coords[1], coords[0]);
}
function getRoadName(properties) {
    const value =
        properties &&
        (properties.Road_Name ||
            properties.road_name ||
            properties.ROAD_NAME ||
            properties.name);
    return value && String(value).trim()
        ? String(value).trim()
        : "unnamed road";
}
function getRoadId(properties, fallback) {
    const value =
        properties &&
        (properties.Road_ID ||
            properties.road_id ||
            properties.ROAD_ID ||
            properties.ID ||
            properties.OBJECTID);
    return value == null || value === "" ? fallback : String(value);
}
function nodeKeyFromCoordinate(coordinate) {
    const longitude = Number(coordinate[0]);
    const latitude = Number(coordinate[1]);
    if (!Number.isFinite(longitude) || !Number.isFinite(latitude)) return null;
    return (
        longitude.toFixed(CONFIG.networkNodePrecision) +
        "," +
        latitude.toFixed(CONFIG.networkNodePrecision)
    );
}
function debugConnectivity(startKey, endKey) {
    const startComp = networkComponentByNode[startKey];
    const endComp = networkComponentByNode[endKey];
    console.log("Start Node:", startKey, "-> Component ID:", startComp);
    console.log("End Node:", endKey, "-> Component ID:", endComp);
    
    if (startComp !== endComp) {
        console.warn("ROUTING ALERT: These points are on disconnected graph islands.");
        showRouteMessage("Routing failed: These points are not connected in the road network.", "error");
    }
}
// ==========================================
// Pointer Events & Cursor Global Functions
// ==========================================
function setDataLayerClicksEnabled(enabled) {
    dataLayers.forEach((group) => {
        group.eachLayer((layer) => {
            const element =
                typeof layer.getElement === "function"
                    ? layer.getElement()
                    : null;

            if (element) {
                element.style.pointerEvents = enabled ? "" : "none";
            }
        });
    });
}

function setRoutingCursor(active) {
    if (map && map.getContainer()) {
        map.getContainer().style.cursor = active ? "crosshair" : "";
    }
}

// ==========================================
// NAS Street-address Index, Autocomplete & Reverse Lookup
// ==========================================
function formatNasAddress(address) {
    if (!address) return "No nearby street address";
    const main =
        address.streetAddress ||
        [address.houseNumber, address.roadName].filter(Boolean).join(" ");
    return (
        [main, address.areaName, address.postcode].filter(Boolean).join(", ") ||
        "No nearby street address"
    );
}
function buildNasAddressIndex() {
    nasAddressIndex = [];
    if (typeof BTNas === "undefined" || !Array.isArray(BTNas.features)) return;
    BTNas.features.forEach((feature, index) => {
        const coordinate = getAddressCoordinate(feature);
        if (
            !coordinate ||
            !Number.isFinite(Number(coordinate[0])) ||
            !Number.isFinite(Number(coordinate[1]))
        )
            return;
        const props = feature.properties || {};
        const houseNumber = getNasProperty(props, [
            "House_Numb",
            "House Number",
            "House_No",
            "HouseNo",
        ]);
        const roadName = getNasProperty(props, [
            "Road_Name",
            "Road Name",
            "Street_Name",
            "Street Name",
        ]);
        const streetAddress =
            getNasProperty(props, [
                "Street_Add",
                "Street Address",
                "Address",
            ]) || [houseNumber, roadName].filter(Boolean).join(" ");
        const areaName = getNasProperty(props, [
            "Area_Name",
            "Area Name",
            "Locality",
            "Suburb",
        ]);
        const postcode = getNasProperty(props, [
            "Postcode",
            "Post Code",
            "Postal Code",
        ]);
        const display = formatNasAddress({
            houseNumber,
            roadName,
            streetAddress,
            areaName,
            postcode,
        });
        const searchText = [
            display,
            streetAddress,
            houseNumber,
            "House " + houseNumber,
            roadName,
            areaName,
            postcode,
        ]
            .join(" ")
            .toLowerCase();
        nasAddressIndex.push({
            id: index,
            lng: Number(coordinate[0]),
            lat: Number(coordinate[1]),
            houseNumber: String(houseNumber),
            roadName: String(roadName),
            streetAddress: String(streetAddress),
            areaName: String(areaName),
            postcode: String(postcode),
            display,
            searchText,
        });
    });
    console.info(
        "NAS address index ready:",
        nasAddressIndex.length,
        "searchable address features."
    );
    if (!nasAddressIndex.length) {
        console.warn(
            "No searchable NAS addresses were indexed. Check the BTNas GeoJSON variable and feature properties."
        );
    }
}
function findNasAddressMatches(query, limit) {
    const words = String(query || "")
        .trim()
        .toLowerCase()
        .split(/\s+/)
        .filter(Boolean);
    if (!words.length) return [];
    const matches = nasAddressIndex
        .filter((address) =>
            words.every((word) => address.searchText.includes(word))
        )
        .map((address) => {
            const exact = [
                address.streetAddress,
                address.display,
                address.houseNumber,
                "house " + address.houseNumber,
            ].some(
                (value) =>
                    String(value).toLowerCase() ===
                    String(query).trim().toLowerCase()
            );
            const startsWith = address.display
                .toLowerCase()
                .startsWith(String(query).trim().toLowerCase());
            return {
                address,
                score:
                    (exact ? 100 : 0) +
                    (startsWith ? 20 : 0) -
                    address.display.length / 10000,
            };
        })
        .sort((a, b) => b.score - a.score)
        .map((result) => result.address);
    return typeof limit === "number" ? matches.slice(0, limit) : matches;
}
function findNearestNasAddress(latlng) {
    if (!nasAddressIndex.length) return null;
    const point = turf.point([latlng.lng, latlng.lat]);
    let nearest = null;
    let shortestDistance = Infinity;
    nasAddressIndex.forEach((address) => {
        const distance = turf.distance(
            point,
            turf.point([address.lng, address.lat]),
            { units: "kilometers" }
        );
        if (distance < shortestDistance) {
            shortestDistance = distance;
            nearest = address;
        }
    });
    return nearest ? { address: nearest, distance: shortestDistance } : null;
}
// ==========================================
// Routing Graph
// ==========================================
function addGraphEdge(fromCoordinate, toCoordinate, properties, featureIndex) {
    const fromKey = nodeKeyFromCoordinate(fromCoordinate);
    const toKey = nodeKeyFromCoordinate(toCoordinate);
    if (!fromKey || !toKey || fromKey === toKey) return;
    
    const fromPoint = turf.point(fromCoordinate);
    const toPoint = turf.point(toCoordinate);
    const distance = turf.distance(fromPoint, toPoint, { units: "kilometers" });
    const roadName = getRoadName(properties);
    const roadId = getRoadId(properties, "feature-" + featureIndex);
    
    if (!networkGraph[fromKey]) networkGraph[fromKey] = [];
    if (!networkGraph[toKey]) networkGraph[toKey] = [];

    // 1. Detect your exact 'Oneway' property and normalise it to uppercase
    const rawOneway = properties && properties.Oneway ? String(properties.Oneway).toUpperCase().trim() : '';
    
    // Fallback: If the cell is blank or unpopulated, default it to 'BOTH' (two-way)
    const oneway = rawOneway || 'BOTH';

    // 2. Forward Direction (From -> To): Allowed on 'FT' and 'BOTH' streets
    const canTravelForward = oneway === 'FT' || oneway === 'BOTH';
    
    if (canTravelForward) {
        networkGraph[fromKey].push({
            to: toKey,
            dist: distance,
            roadName,
            roadId,
            bearing: turf.bearing(fromPoint, toPoint),
            geometry: [fromCoordinate, toCoordinate],
        });
    }

    // 3. Reverse Direction (To -> From): Allowed on 'TF' and 'BOTH' streets
    const canTravelReverse = oneway === 'TF' || oneway === 'BOTH';

    if (canTravelReverse) {
        networkGraph[toKey].push({
            to: fromKey,
            dist: distance,
            roadName,
            roadId,
            bearing: turf.bearing(toPoint, fromPoint),
            geometry: [toCoordinate, fromCoordinate],
        });
    }
}
function indexNetworkComponents() {
    networkComponentByNode = {};
    let componentCount = 0;
    let largestComponentSize = 0;
    Object.keys(networkGraph).forEach((nodeKey) => {
        if (networkComponentByNode[nodeKey] !== undefined) return;
        const pending = [nodeKey];
        let componentSize = 0;
        networkComponentByNode[nodeKey] = componentCount;
        while (pending.length) {
            const currentKey = pending.pop();
            componentSize++;
            (networkGraph[currentKey] || []).forEach((edge) => {
                const destination = edge.to || edge.id;
                if (networkComponentByNode[destination] === undefined) {
                    networkComponentByNode[destination] = componentCount;
                    pending.push(destination);
                }
            });
        }
        largestComponentSize = Math.max(largestComponentSize, componentSize);
        componentCount++;
    });
    console.info(
        "Routing graph ready:",
        Object.keys(networkGraph).length + " nodes,",
        componentCount + " connected components,",
        largestComponentSize + " nodes in the largest component."
    );
}
function buildNetworkGraph() {
    networkGraph = {};
    networkComponentByNode = {};
    if (typeof BTRoads === "undefined" || !Array.isArray(BTRoads.features))
        return;
    BTRoads.features.forEach((feature, featureIndex) => {
        if (!feature.geometry) return;
        const properties = feature.properties || {};
        const processLine = (coordinates) => {
            if (!Array.isArray(coordinates)) return;
            for (let index = 0; index < coordinates.length - 1; index++) {
                addGraphEdge(
                    coordinates[index],
                    coordinates[index + 1],
                    properties,
                    featureIndex
                );
            }
        };
        if (feature.geometry.type === "LineString")
            processLine(feature.geometry.coordinates);
        if (feature.geometry.type === "MultiLineString")
            feature.geometry.coordinates.forEach(processLine);
    });
    indexNetworkComponents();
}
function findNearestNetworkNode(latlng) {
    const keys = Object.keys(networkGraph);
    if (!keys.length) return null;
    const point = turf.point([latlng.lng, latlng.lat]);
    let nearestKey = null;
    let shortestDistance = Infinity;
    keys.forEach((key) => {
        const coordinate = key.split(",").map(Number);
        const distance = turf.distance(point, turf.point(coordinate), {
            units: "kilometers",
        });
        if (distance < shortestDistance) {
            shortestDistance = distance;
            nearestKey = key;
        }
    });
    return nearestKey;
}
// Heap-based Dijkstra returns both the node geometry and the metadata-rich edges used for directions.
// It remains responsive for the 60,000+ vertices in the BTRoads dataset.
function computeShortestPath(startKey, endKey) {
    if (!networkGraph[startKey] || !networkGraph[endKey]) return null;
    if (networkComponentByNode[startKey] !== networkComponentByNode[endKey])
        return null;
    class MinHeap {
        constructor() {
            this.items = [];
        }
        get size() {
            return this.items.length;
        }
        push(item) {
            this.items.push(item);
            let index = this.items.length - 1;
            while (index > 0) {
                const parent = Math.floor((index - 1) / 2);
                if (this.items[parent].distance <= item.distance) break;
                this.items[index] = this.items[parent];
                index = parent;
            }
            this.items[index] = item;
        }
        pop() {
            if (!this.items.length) return null;
            const minimum = this.items[0];
            const last = this.items.pop();
            if (this.items.length) {
                let index = 0;
                while (index * 2 + 1 < this.items.length) {
                    let child = index * 2 + 1;
                    if (
                        child + 1 < this.items.length &&
                        this.items[child + 1].distance <
                            this.items[child].distance
                    )
                        child++;
                    if (this.items[child].distance >= last.distance) break;
                    this.items[index] = this.items[child];
                    index = child;
                }
                this.items[index] = last;
            }
            return minimum;
        }
    }
    const distances = { [startKey]: 0 };
    const previousNode = {};
    const previousEdge = {};
    const pending = new MinHeap();
    pending.push({ key: startKey, distance: 0 });
    while (pending.size) {
        const current = pending.pop();
        const currentKey = current.key;
        if (current.distance !== distances[currentKey]) continue; // Superseded queue entry.
        if (currentKey === endKey) break;
        (networkGraph[currentKey] || []).forEach((edge) => {
            const destination = edge.to || edge.id; // id retained only for compatibility with older saved graphs.
            const alternative = current.distance + edge.dist;
            if (
                alternative <
                (distances[destination] === undefined
                    ? Infinity
                    : distances[destination])
            ) {
                distances[destination] = alternative;
                previousNode[destination] = currentKey;
                previousEdge[destination] = edge;
                pending.push({ key: destination, distance: alternative });
            }
        });
    }
    if (distances[endKey] === undefined) return null;
    const nodeKeys = [endKey];
    const edges = [];
    let key = endKey;
    while (key !== startKey) {
        if (!previousNode[key] || !previousEdge[key]) return null;
        edges.unshift(previousEdge[key]);
        key = previousNode[key];
        nodeKeys.unshift(key);
    }
    const lngLatPath = [];
    edges.forEach((edge, index) => {
        const geometry =
            edge.geometry && edge.geometry.length
                ? edge.geometry
                : [
                      nodeKeys[index].split(",").map(Number),
                      nodeKeys[index + 1].split(",").map(Number),
                  ];
        if (!index) lngLatPath.push(...geometry);
        else lngLatPath.push(...geometry.slice(1));
    });
    if (!lngLatPath.length) lngLatPath.push(startKey.split(",").map(Number));
    return {
        nodeKeys,
        edges,
        distance: distances[endKey],
        latLngs: lngLatPath.map((coordinate) => [coordinate[1], coordinate[0]]),
    };
}
function normaliseBearingDifference(fromBearing, toBearing) {
    return ((toBearing - fromBearing + 540) % 360) - 180;
}
function getTurnInstruction(previousBearing, nextBearing) {
    const difference = normaliseBearingDifference(previousBearing, nextBearing);
    const absoluteDifference = Math.abs(difference);
    if (absoluteDifference < 20) return "Continue";
    if (absoluteDifference < 60)
        return "Slight " + (difference > 0 ? "right" : "left");
    if (absoluteDifference < 120)
        return "Turn " + (difference > 0 ? "right" : "left");
    if (absoluteDifference < 170)
        return "Sharp " + (difference > 0 ? "right" : "left");
    return "Make a U-turn";
}
function buildDirections(edges) {
    if (!edges.length) return [];
    
    const groups = [];
    
    // 1. Group edges together (your existing logic)
    edges.forEach((edge) => {
        const roadName = edge.roadName || "unnamed road";
        const roadKey = edge.roadId || roadName.toLowerCase();
        const previous = groups[groups.length - 1];
        
        if (
            previous &&
            previous.roadKey === roadKey &&
            previous.roadName.toLowerCase() === roadName.toLowerCase()
        ) {
            previous.distance += edge.dist;
            previous.exitBearing = edge.bearing;
        } else {
            groups.push({
                roadKey,
                roadName,
                distance: edge.dist,
                entryBearing: edge.bearing,
                exitBearing: edge.bearing,
            });
        }
    });
    
    // 2. Generate raw instructions (your existing logic)
    const rawDirections = groups.map((group, index) => {
        const action =
            index === 0
                ? "Continue"
                : getTurnInstruction(
                      groups[index - 1].exitBearing,
                      group.entryBearing
                  );
        return {
            action,
            roadName: group.roadName,
            distance: group.distance,
            text:
                action === "Continue"
                    ? "Continue on " + group.roadName
                    : action === "Make a U-turn"
                      ? "Make a U-turn onto " + group.roadName
                      : action + " onto " + group.roadName,
        };
    });

    // 3. NEW LOGIC: Merge consecutive "Continue" instructions on the same road
    const mergedDirections = [];
    
    rawDirections.forEach((direction) => {
        const previous = mergedDirections[mergedDirections.length - 1];
        
        // If the previous step and the current step are BOTH "Continue" on the same road...
        if (
            previous && 
            previous.action === "Continue" && 
            direction.action === "Continue" && 
            previous.roadName.toLowerCase() === direction.roadName.toLowerCase()
        ) {
            // ...just add the distance to the existing instruction!
            previous.distance += direction.distance;
        } else {
            // Otherwise, push it as a new distinct step
            mergedDirections.push({ ...direction });
        }
    });

    return mergedDirections;
}
function destinationSide(lastEdge) {
    if (!lastEdge || !routingState.endActualLatLng)
        return "Destination reached";
    const lastRoadCoordinate =
        lastEdge.geometry && lastEdge.geometry[lastEdge.geometry.length - 1];
    if (!lastRoadCoordinate) return "Destination reached";
    if (
        turf.distance(
            turf.point(lastRoadCoordinate),
            turf.point([
                routingState.endActualLatLng.lng,
                routingState.endActualLatLng.lat,
            ]),
            { units: "kilometers" }
        ) < 0.00002
    )
        return "Destination reached";
    const bearingToDestination = turf.bearing(
        turf.point(lastRoadCoordinate),
        turf.point([
            routingState.endActualLatLng.lng,
            routingState.endActualLatLng.lat,
        ])
    );
    const difference = normaliseBearingDifference(
        lastEdge.bearing,
        bearingToDestination
    );
    return "Destination is on the " + (difference >= 0 ? "right" : "left");
}
// ==========================================
// Route Planner UI (created in JavaScript so no HTML changes are required)
// ==========================================
function showRouteMessage(message, type) {
    const panel = document.getElementById("route-summary-panel");
    if (!panel) return;
    panel.innerHTML =
        "<div class='route-message " +
        (type || "info") +
        "'>" +
        escapeHtml(message) +
        "</div>";
}
function endpointFields(kind) {
    return {
        address: document.getElementById(kind + "-address-input"),
        latitude: document.getElementById(kind + "-latitude-input"),
        longitude: document.getElementById(kind + "-longitude-input"),
        easting: document.getElementById(kind + "-easting-input"),
        northing: document.getElementById(kind + "-northing-input"),
        hint: document.getElementById(kind + "-address-hint"),
    };
}
function updateEndpointHint(kind, nearestNas) {
    const fields = endpointFields(kind);
    if (!fields.hint) return;
    if (!nearestNas) {
        fields.hint.textContent = "No NAS address found.";
        return;
    }
    fields.hint.textContent =
        "Nearest NAS address: " +
        formatNasAddress(nearestNas.address) +
        " (" +
        formatDistance(nearestNas.distance) +
        ")";
}
function syncEndpointCoordinates(kind, latlng) {
    const fields = endpointFields(kind);
    if (fields.latitude) fields.latitude.value = latlng.lat.toFixed(6);
    if (fields.longitude) fields.longitude.value = latlng.lng.toFixed(6);
}
function endpointMarkerIcon(kind) {
    const isStart = kind === "start";
    return L.divIcon({
        className: "route-endpoint-marker",
        html:
            "<span style='display:block;width:28px;height:28px;line-height:28px;border-radius:50%;" +
            "text-align:center;font-weight:700;color:#fff;border:2px solid #fff;box-shadow:0 1px 4px #333;" +
            "background:" +
            (isStart ? "#218739" : "#c42b3b") +
            "'>" +
            (isStart ? "S" : "E") +
            "</span>",
        iconSize: [28, 28],
        iconAnchor: [14, 14],
    });
}
function setRouteEndpoint(kind, coordinate, source) {
    const latlng = L.latLng(coordinate);
    const nodeKey = findNearestNetworkNode(latlng);
    if (!nodeKey) {
        showRouteMessage(
            "The road network is unavailable, so a " +
                kind +
                " point could not be routed.",
            "error"
        );
        return false;
    }
    const isStart = kind === "start";
    const markerKey = isStart ? "startMarker" : "endMarker";
    const nodeKeyName = isStart ? "startNodeKey" : "endNodeKey";
    const actualKey = isStart ? "startActualLatLng" : "endActualLatLng";
    const previousMarker = routingState[markerKey];
    if (previousMarker && map.hasLayer(previousMarker))
        map.removeLayer(previousMarker);
    routingState[nodeKeyName] = nodeKey;
    routingState[actualKey] = latlng;
    const nearestNas = findNearestNasAddress(latlng);
    const nodeLatLng = getNodeLatLng(nodeKey);
    const markerPopup =
        "<b>" +
        (isStart ? "Start" : "End") +
        " location</b><br>" +
        "Actual coordinate: " +
        latlng.lat.toFixed(6) +
        ", " +
        latlng.lng.toFixed(6) +
        "<br>" +
        "Routing node: " +
        nodeLatLng.lat.toFixed(6) +
        ", " +
        nodeLatLng.lng.toFixed(6) +
        "<br>" +
        (nearestNas
            ? "Nearest address: " +
              escapeHtml(formatNasAddress(nearestNas.address))
            : "No nearby NAS address");
    routingState[markerKey] = L.marker(latlng, {
        icon: endpointMarkerIcon(kind),
        title: isStart ? "Start" : "End",
    })
        .addTo(map)
        .bindPopup(markerPopup)
        .openPopup();
    syncEndpointCoordinates(kind, latlng);
    updateEndpointHint(kind, nearestNas);
    routingState.activeMode = null;
    const button = document.getElementById(
        isStart ? "set-start-btn" : "set-end-btn"
    );
    if (button) button.style.background = "";
	setDataLayerClicksEnabled(true);
	setRoutingCursor(false);
    if (source && source.zoom) map.flyTo(latlng, 18);
    return true;
}
function parseEndpointForm(kind) {
    const fields = endpointFields(kind);
    const address = fields.address ? fields.address.value.trim() : "";
    const latitudeText = fields.latitude ? fields.latitude.value.trim() : "";
    const longitudeText = fields.longitude ? fields.longitude.value.trim() : "";
    const eastingText = fields.easting ? fields.easting.value.trim() : "";
    const northingText = fields.northing ? fields.northing.value.trim() : "";
    if (latitudeText || longitudeText) {
        if (!latitudeText || !longitudeText) {
            showRouteMessage(
                "Enter both latitude and longitude for the " +
                    kind +
                    " location.",
                "error"
            );
            return null;
        }
        const lat = Number(latitudeText);
        const lng = Number(longitudeText);
        if (
            !Number.isFinite(lat) ||
            !Number.isFinite(lng) ||
            lat < -90 ||
            lat > 90 ||
            lng < -180 ||
            lng > 180
        ) {
            showRouteMessage(
                "The " + kind + " latitude/longitude values are invalid.",
                "error"
            );
            return null;
        }
        return { latlng: L.latLng(lat, lng), source: "Latitude/longitude" };
    }
    if (eastingText || northingText) {
        if (!eastingText || !northingText) {
            showRouteMessage(
                "Enter both UTM easting and northing for the " +
                    kind +
                    " location.",
                "error"
            );
            return null;
        }
        try {
            const projected = proj4("EPSG:32736", "WGS84", [
                Number(eastingText),
                Number(northingText),
            ]);
            const lng = projected[0];
            const lat = projected[1];
            if (
                !Number.isFinite(lat) ||
                !Number.isFinite(lng) ||
                lat < CONFIG.malawiBounds.latMin ||
                lat > CONFIG.malawiBounds.latMax ||
                lng < CONFIG.malawiBounds.lonMin ||
                lng > CONFIG.malawiBounds.lonMax
            ) {
                showRouteMessage(
                    "The converted UTM coordinate is outside Malawi.",
                    "error"
                );
                return null;
            }
            return { latlng: L.latLng(lat, lng), source: "UTM 36S" };
        } catch (error) {
            console.error("UTM conversion error:", error);
            showRouteMessage(
                "The " + kind + " UTM coordinate could not be converted.",
                "error"
            );
            return null;
        }
    }
    if (address) {
        const match = findNasAddressMatches(address, 1)[0];
        if (!match) {
            showRouteMessage(
                'No NAS street address matches "' + address + '".',
                "error"
            );
            return null;
        }
        return {
            latlng: L.latLng(match.lat, match.lng),
            source: "NAS address",
            address: match,
        };
    }
    showRouteMessage(
        "Enter a street address, latitude/longitude, or UTM coordinate for the " +
            kind +
            " location.",
        "error"
    );
    return null;
}
function locateRouteEndpoint(kind) {
    const selection = parseEndpointForm(kind);
    if (!selection) return;
    if (setRouteEndpoint(kind, selection.latlng, { zoom: true })) {
        const fields = endpointFields(kind);
        if (selection.address && fields.address)
            fields.address.value = selection.address.display;
    }
}
function populateAddressDatalists() {
    ["start", "end"].forEach((kind) => {
        const list = document.getElementById(kind + "-address-list");
        if (!list) return;
        list.innerHTML = "";
        const uniqueDisplays = new Set();
        nasAddressIndex.forEach((address) => {
            if (uniqueDisplays.size < 2000) uniqueDisplays.add(address.display);
        });
        uniqueDisplays.forEach((display) => {
            const option = document.createElement("option");
            option.value = display;
            list.appendChild(option);
        });
    });
}
function initialiseAddressAutocomplete(kind) {
    const fields = endpointFields(kind);
    if (!fields.address || typeof Awesomplete === "undefined") return;
    const autocomplete = new Awesomplete(fields.address, {
        minChars: 1,
        maxItems: 20,
        filter: () => true,
    });
    const update = debounce(() => {
        const query = fields.address.value.trim();
        autocomplete.list = findNasAddressMatches(query, 50).map(
            (address) => address.display
        );
        autocomplete.evaluate();
    }, 150);
    fields.address.addEventListener("input", update);
}
function setupRoutePlannerUI() {
    if (document.getElementById("route-planner-panel")) return;
    const clearButton = document.getElementById("clear-route-btn");
    const insertionPoint = clearButton && clearButton.parentElement;
    if (!insertionPoint) return;
    const style = document.createElement("style");
    style.id = "route-planner-styles";
    style.textContent = [
        "#route-planner-panel{margin-top:12px;padding:12px;background:#fff;border:1px solid #d9dde3;border-radius:6px;font:13px/1.4 Arial,sans-serif;max-width:430px}",
        "#route-planner-panel h3{margin:0 0 8px;font-size:15px}",
        ".route-location{padding:10px 0;border-top:1px solid #e6e9ed}",
        ".route-location:first-of-type{border-top:0}",
        ".route-location label{display:block;margin:6px 0 2px;font-weight:600}",
        ".route-location input{box-sizing:border-box;width:100%;padding:6px;border:1px solid #bfc7d1;border-radius:3px}",
        ".route-coordinate-row{display:grid;grid-template-columns:1fr 1fr;gap:7px}",
        ".route-or{text-align:center;color:#6b7280;font-weight:700;margin:8px 0 2px}",
        ".route-locate{margin-top:8px;padding:6px 14px;cursor:pointer}",
        ".route-address-hint{display:block;margin-top:6px;color:#4b5563}",
        "#route-summary-panel{margin-top:12px;border-top:1px solid #d9dde3;padding-top:10px}",
        ".route-summary-grid{display:grid;grid-template-columns:1fr auto;gap:4px 12px;margin:8px 0}",
        ".route-summary-grid strong{font-weight:700}",
        ".route-directions{padding-left:22px;margin:8px 0 0}",
        ".route-directions li{margin:0 0 9px;padding-left:2px}",
        ".route-direction-distance{display:block;color:#4b5563;font-size:12px}",
        ".route-message{padding:8px;border-radius:4px;background:#eef4ff;color:#1d4f91}",
        ".route-message.error{background:#fce9e9;color:#9b1c1c}",
    ].join("");
    document.head.appendChild(style);
    const panel = document.createElement("section");
    panel.id = "route-planner-panel";
    panel.setAttribute("aria-label", "Route location and directions");
    panel.innerHTML =
        "<h3>Route Locations</h3>" +
        "<div class='route-location'>" +
        "<strong>START</strong>" +
        "<label for='start-address-input'>Street Address</label>" +
        "<input id='start-address-input' list='start-address-list' autocomplete='off' placeholder='16 Independence Drive'>" +
        "<datalist id='start-address-list'></datalist>" +
        "<div class='route-coordinate-row'><div><label for='start-latitude-input'>Latitude</label><input id='start-latitude-input' inputmode='decimal' placeholder='-15.789234'></div>" +
        "<div><label for='start-longitude-input'>Longitude</label><input id='start-longitude-input' inputmode='decimal' placeholder='35.034221'></div></div>" +
        "<div class='route-or'>OR</div>" +
        "<div class='route-coordinate-row'><div><label for='start-easting-input'>UTM Easting</label><input id='start-easting-input' inputmode='decimal' placeholder='503234'></div>" +
        "<div><label for='start-northing-input'>UTM Northing</label><input id='start-northing-input' inputmode='decimal' placeholder='8256345'></div></div>" +
        "<button id='locate-start-btn' class='route-locate' type='button'>Locate Start</button><small id='start-address-hint' class='route-address-hint'></small>" +
        "</div>" +
        "<div class='route-location'>" +
        "<strong>END</strong>" +
        "<label for='end-address-input'>Street Address</label>" +
        "<input id='end-address-input' list='end-address-list' autocomplete='off' placeholder='54 Glyn Jones Road'>" +
        "<datalist id='end-address-list'></datalist>" +
        "<div class='route-coordinate-row'><div><label for='end-latitude-input'>Latitude</label><input id='end-latitude-input' inputmode='decimal'></div>" +
        "<div><label for='end-longitude-input'>Longitude</label><input id='end-longitude-input' inputmode='decimal'></div></div>" +
        "<div class='route-or'>OR</div>" +
        "<div class='route-coordinate-row'><div><label for='end-easting-input'>UTM Easting</label><input id='end-easting-input' inputmode='decimal'></div>" +
        "<div><label for='end-northing-input'>UTM Northing</label><input id='end-northing-input' inputmode='decimal'></div></div>" +
        "<button id='locate-end-btn' class='route-locate' type='button'>Locate End</button><small id='end-address-hint' class='route-address-hint'></small>" +
        "</div>" +
        "<section id='route-summary-panel' aria-live='polite'><div class='route-message'>Set a start and end location, then calculate the route.</div></section>";
    insertionPoint.insertAdjacentElement("afterend", panel);
    populateAddressDatalists();
    initialiseAddressAutocomplete("start");
    initialiseAddressAutocomplete("end");
    document
        .getElementById("locate-start-btn")
        .addEventListener("click", () => locateRouteEndpoint("start"));
    document
        .getElementById("locate-end-btn")
        .addEventListener("click", () => locateRouteEndpoint("end"));
}
function renderRouteSummary(path) {
    const panel = document.getElementById("route-summary-panel");
    if (!panel) return;
    const directions = buildDirections(path.edges);
    const travelTimes = [
        { label: "Walking (5 km/h)", speed: 5 },
        { label: "Cycling (15 km/h)", speed: 15 },
        { label: "Driving (45 km/h)", speed: 45 },
    ];
    const directionMarkup = directions
        .map(
            (direction, index) =>
                "<li><strong>" +
                escapeHtml(direction.text) +
                "</strong><span class='route-direction-distance'>" +
                formatDistance(direction.distance) +
                "</span></li>"
        )
        .join("");
    const timeMarkup = travelTimes
        .map(
            (item) =>
                "<div>" +
                item.label +
                " (average " +
                item.speed +
                " km/h)</div><strong>" +
                formatDuration(path.distance / item.speed) +
                "</strong>"
        )
        .join("");
    const endText = destinationSide(path.edges[path.edges.length - 1]);
    panel.innerHTML =
        "<h3>Route Summary</h3>" +
        "<div class='route-summary-grid'><div>Distance</div><strong>" +
        formatDistance(path.distance) +
        "</strong>" +
        timeMarkup +
        "</div>" +
        "<h3>Directions</h3><ol class='route-directions'>" +
        directionMarkup +
        "<li><strong>" +
        escapeHtml(endText) +
        "</strong></li></ol>";
}
// ==========================================
// Route rendering and state management
// ==========================================
function removeLayerFromMap(layerName) {
    if (routingState[layerName] && map && map.hasLayer(routingState[layerName]))
        map.removeLayer(routingState[layerName]);
    routingState[layerName] = null;
}
function clearRouteDrawing() {
    removeLayerFromMap("routeLine");
    removeLayerFromMap("startConnector");
    removeLayerFromMap("endConnector");
}
function clearCalculatedRouteUI() {
    routingState.activeMode = null;
    routingState.startNodeKey = null;
    routingState.endNodeKey = null;
    routingState.startActualLatLng = null;
    routingState.endActualLatLng = null;
    removeLayerFromMap("startMarker");
    removeLayerFromMap("endMarker");
    clearRouteDrawing();
    ["start", "end"].forEach((kind) => {
        const fields = endpointFields(kind);
        ["address", "latitude", "longitude", "easting", "northing"].forEach(
            (name) => {
                if (fields[name]) fields[name].value = "";
            }
        );
        if (fields.hint) fields.hint.textContent = "";
    });
    const startButton = document.getElementById("set-start-btn");
    const endButton = document.getElementById("set-end-btn");
    if (startButton) startButton.style.background = "";
    if (endButton) endButton.style.background = "";
    showRouteMessage("Set a start and end location, then calculate the route.");
	setDataLayerClicksEnabled(true);
	setRoutingCursor(false);
}
function drawConnector(layerName, actualLatLng, nodeKey) {
    const nodeLatLng = getNodeLatLng(nodeKey);
    if (actualLatLng.distanceTo(nodeLatLng) < 0.05) return;
    routingState[layerName] = L.polyline(
        [actualLatLng, nodeLatLng],
        CONFIG.styles.connector
    ).addTo(map);
}
function calculateAndDisplayRoute() {
    if (
        !routingState.startNodeKey ||
        !routingState.endNodeKey ||
        !routingState.startActualLatLng ||
        !routingState.endActualLatLng
    ) {
        showRouteMessage(
            "Please set both the start and end locations before calculating a route.",
            "error"
        );
        return;
    }
    clearRouteDrawing();
	debugConnectivity(routingState.startNodeKey, routingState.endNodeKey);
    const path = computeShortestPath(
        routingState.startNodeKey,
        routingState.endNodeKey
    );
    if (!path || !path.latLngs.length) {
        showRouteMessage(
            "No route is available between these network locations.",
            "error"
        );
        return;
    }
    routingState.routeLine = L.polyline(
        path.latLngs,
        CONFIG.styles.route
    ).addTo(map);
    drawConnector(
        "startConnector",
        routingState.startActualLatLng,
        routingState.startNodeKey
    );
    drawConnector(
        "endConnector",
        routingState.endActualLatLng,
        routingState.endNodeKey
    );
    const routeLayers = [
        routingState.routeLine,
        routingState.startConnector,
        routingState.endConnector,
    ].filter(Boolean);
    map.fitBounds(L.featureGroup(routeLayers).getBounds(), {
        padding: [40, 40],
    });
    renderRouteSummary(path);
}
// ==========================================
// Main Initialization
// ==========================================
function initialize() {
    map = L.map("mapdiv", { zoomControl: false }).setView(
        CONFIG.startCoords,
        CONFIG.startZoom
    );
    proj4.defs("EPSG:32736", CONFIG.utm36S);
    // ====================== MEASURE PLUGIN FIX ======================
    L.Control.Measure.include({
        _setCaptureMarkerIcon: function () {
            // Prevent auto-panning/jumping when the capture marker is placed
            if (this._captureMarker) {
                this._captureMarker.options.autoPanOnFocus = false;
                this._captureMarker.options.autoPan = false;
            }
            // Use the original large invisible capture icon
            this._captureMarker.setIcon(
                L.divIcon({
                    iconSize: this._map.getSize().multiplyBy(2),
                    className: "leaflet-measure-capture-marker",
                })
            );
        },
    });
    // ================================================================
    L.control.zoom({ position: "bottomleft" }).addTo(map);
    L.control
        .locate({
            position: "bottomleft",
            // The location marker may update, but it must never move the map.
            setView: false,
            flyTo: false,
            keepCurrentZoomLevel: true,
            locateOptions: {
                enableHighAccuracy: true,
                maxZoom: 18,
                watch: false,
            },
        })
        .addTo(map);
    function handleNormalMapClick(event) {
        if (isMeasuring) return;
        if (routingState.activeMode === "start") {
            setRouteEndpoint("start", event.latlng, { source: "Map click" });
        } else if (routingState.activeMode === "end") {
            setRouteEndpoint("end", event.latlng, { source: "Map click" });
        } else {
            map.closePopup();
            clearSearchMarkers();
            clearHighlights();
        }
    }
    
    function enableNormalMapClicks() {
        map.off("click", handleNormalMapClick);
        map.on("click", handleNormalMapClick);
    }
    enableNormalMapClicks();

    let restoreNormalMapClicksTimer;
    const measureControl = new L.Control.Measure({
        primaryLengthUnit: "meters",
        secondaryLengthUnit: "kilometers",
        primaryAreaUnit: "sqmeters",
        secondaryAreaUnit: "hectares",
        activeColor: "#db4a44",
        completedColor: "#8b2412",
        captureZIndex: 10000,
        popupOptions: {
            autoPan: false,
            closeOnClick: false,
        },
    }).addTo(map);
    
    map.on("measurestart", () => {
        isMeasuring = true;
        clearTimeout(restoreNormalMapClicksTimer);
        // Clear interfering states
        routingState.activeMode = null;
        map.closePopup();
        clearSearchMarkers();
        clearHighlights();
        // Disable data layer clicks
        setDataLayerClicksEnabled(false);
        // Reset routing buttons
        ["set-start-btn", "set-end-btn"].forEach((id) => {
            const button = document.getElementById(id);
            if (button) button.style.background = "";
        });
        map.off("click", handleNormalMapClick);
    });
    map.on("measurefinish", () => {
        clearTimeout(restoreNormalMapClicksTimer);
        // Small delay helps avoid race conditions with the plugin
        restoreNormalMapClicksTimer = window.setTimeout(() => {
            isMeasuring = false;
            setDataLayerClicksEnabled(true);
            enableNormalMapClicks();
        }, 10); // 10ms is usually enough
    });
    const basemaps = {
        "Open Street Map": L.tileLayer(
            "https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png",
            {
                attribution: "Map data © OpenStreetMap contributors",
                maxZoom: CONFIG.maxZoom,
            }
        ).addTo(map),
        "Google Satellite": L.tileLayer(
            "https://mt1.google.com/vt/lyrs=s&x={x}&y={y}&z={z}",
            {
                attribution: "© Google Maps",
                maxZoom: CONFIG.maxZoom,
            }
        ),
        "Google Satellite Hybrid": L.tileLayer(
            "https://mt1.google.com/vt/lyrs=s,h&x={x}&y={y}&z={z}",
            {
                attribution: "© Google Maps",
                maxZoom: CONFIG.maxZoom,
            }
        ),
    };
    const boundaryLayer = L.geoJSON(BTBoundary, {
        style: CONFIG.styles.boundary,
    }).addTo(map);
    const postcodeLayer = L.geoJSON(BTPostcodes, {
        style: CONFIG.styles.postcode,
        onEachFeature: (feature, layer) => {
            if (!feature.properties) return;
            layer.bindPopup(
                createPopup("Postcode Information", {
                    Postcode: feature.properties.Postcode,
                    "Area Name": feature.properties.Name,
                })
            );
        },
    }).addTo(map);
    const nasLayer = L.geoJSON(BTNas, {
        style: CONFIG.styles.nas,
        onEachFeature: (feature, layer) => {
            if (!feature.properties) return;
            layer.bindPopup(
                createPopup("NAS Information", {
                    "House Number": feature.properties.House_Numb,
                    "Road Name": feature.properties.Road_Name,
                    "Area Name": feature.properties.Area_Name,
                    District: feature.properties.District,
                    Postcode: feature.properties.Postcode,
                })
            );
        },
    }).addTo(map);
    const roadLayer = L.geoJSON(BTRoads, {
        style: CONFIG.styles.road,
        onEachFeature: (feature, layer) => {
            if (feature.properties)
                layer.bindPopup(
                    createPopup("Road Information", {
                        Name: getRoadName(feature.properties),
                    })
                );
        },
    }).addTo(map);

    dataLayers = [boundaryLayer, postcodeLayer, nasLayer, roadLayer];

    map.fitBounds(boundaryLayer.getBounds());
    buildNetworkGraph();
    buildNasAddressIndex();
    L.control
        .layers(basemaps, {
            "BT City Roads": roadLayer,
            "Street Addresses": nasLayer,
            Postcodes: postcodeLayer,
            "BT City Boundary": boundaryLayer,
        })
        .addTo(map);
    const searchInput = document.getElementById("plot-search-input");
    const layerSelect = document.getElementById("layer-select");
    const attributeSelect = document.getElementById("attribute-select");
    const searchButton = document.getElementById("search-button");
    const searchConfig = {
        nas: {
            layer: nasLayer,
            attributes: [
                "plot_no",
                "Street_Add",
                "House_Numb",
                "Road_Name",
                "Area_Name",
                "Postcode",
            ],
        },
        road: { layer: roadLayer, attributes: ["Road_Name"] },
        postcode: { layer: postcodeLayer, attributes: ["Postcode", "Name"] },
    };
    const valueCache = {};
    let previousHighlightLayers = [];
    let previousHighlightGroup = null;
    function updateDropdowns() {
        const config = searchConfig[layerSelect.value];
        if (!config) return;
        attributeSelect.innerHTML = "";
        config.attributes.forEach((attribute) => {
            const option = document.createElement("option");
            option.value = attribute;
            option.textContent = attribute.replace(/_/g, " ");
            attributeSelect.appendChild(option);
        });
        updateDatalist();
    }
    function updateDatalist() {
        const selectedKey = layerSelect.value;
        const selectedAttribute = attributeSelect.value;
        const cacheKey = selectedKey + "-" + selectedAttribute;
        if (!valueCache[cacheKey]) {
            const values = new Set();
            searchConfig[selectedKey].layer.eachLayer((layer) => {
                const value =
                    layer.feature &&
                    layer.feature.properties &&
                    layer.feature.properties[selectedAttribute];
                if (value) values.add(String(value));
            });
            valueCache[cacheKey] = Array.from(values).sort();
        }
    }
    const awesomplete = new Awesomplete(searchInput, {
        minChars: 1,
        maxItems: 200,
        filter: () => true,
    });
    const updateSuggestions = debounce(() => {
        const input = searchInput.value.trim().toLowerCase();
        if (!input) {
            awesomplete.list = [];
            return;
        }
        // The global search obeys the selected layer AND selected field.
        // For Street Addresses this exposes all six NAS attributes independently:
        // plot_no, Street_Add, House_Numb, Road_Name, Area_Name and Postcode.
        const cacheKey = layerSelect.value + "-" + attributeSelect.value;
        const words = input.split(/\s+/).filter(Boolean);
        awesomplete.list = (valueCache[cacheKey] || [])
            .filter((value) =>
                words.every((word) => value.toLowerCase().includes(word))
            )
            .sort((left, right) => {
                const leftStarts = left.toLowerCase().startsWith(input);
                const rightStarts = right.toLowerCase().startsWith(input);
                if (leftStarts !== rightStarts) return leftStarts ? -1 : 1;
                return left.localeCompare(right);
            })
            .slice(0, 200);
        awesomplete.evaluate();
    }, 250);
    function clearHighlights() {
        if (previousHighlightGroup && previousHighlightGroup.resetStyle) {
            previousHighlightLayers.forEach((layer) =>
                previousHighlightGroup.resetStyle(layer)
            );
        }
        previousHighlightLayers = [];
        previousHighlightGroup = null;
    }
    function plotMarkerAndFly(lat, lng, popupHtml) {
        clearSearchMarkers();
        const marker = L.marker([lat, lng])
            .addTo(map)
            .bindPopup(popupHtml)
            .openPopup();
        searchMarkers.push(marker);
        map.flyTo([lat, lng], 18);
    }
    function handleWGS84Search(term) {
        const match = term.match(CONFIG.wgs84Regex);
        if (!match) return false;
        plotMarkerAndFly(
            Number(match[1]),
            Number(match[2]),
            "WGS84 coordinates<br>" +
                escapeHtml(match[1]) +
                ", " +
                escapeHtml(match[2])
        );
        return true;
    }
    function handleUTMSearch(term) {
        const match = term.match(CONFIG.utmRegex);
        if (!match) return false;
        try {
            const projected = proj4("EPSG:32736", "WGS84", [
                Number(match[1]),
                Number(match[2]),
            ]);
            const lng = projected[0];
            const lat = projected[1];
            if (
                lat < CONFIG.malawiBounds.latMin ||
                lat > CONFIG.malawiBounds.latMax ||
                lng < CONFIG.malawiBounds.lonMin ||
                lng > CONFIG.malawiBounds.lonMax
            ) {
                showRouteMessage(
                    "The converted UTM coordinate is outside Malawi.",
                    "error"
                );
                return true;
            }
            plotMarkerAndFly(
                lat,
                lng,
                "<b>UTM 36S</b><br>E: " +
                    escapeHtml(match[1]) +
                    "<br>N: " +
                    escapeHtml(match[2])
            );
        } catch (error) {
            console.error("Projection error:", error);
            showRouteMessage(
                "The UTM coordinate could not be converted.",
                "error"
            );
        }
        return true;
    }
    function handleAttributeSearch(term) {
        // Match only the field the user selected in the top search controls.
        const normalisedTerm = term.replace(/\s/g, "").toLowerCase();
        const targetLayer = searchConfig[layerSelect.value].layer;
        const selectedAttribute = attributeSelect.value;
        clearHighlights();
        const matches = [];
        const bounds = L.latLngBounds();
        targetLayer.eachLayer((layer) => {
            const value =
                layer.feature &&
                layer.feature.properties &&
                layer.feature.properties[selectedAttribute];
            if (
                value &&
                String(value).replace(/\s/g, "").toLowerCase() ===
                    normalisedTerm
            ) {
                if (typeof layer.setStyle === "function")
                    layer.setStyle(CONFIG.styles.highlight);
                matches.push(layer);
                if (layer.getBounds) bounds.extend(layer.getBounds());
                if (layer.getLatLng) bounds.extend(layer.getLatLng());
            }
        });
        if (matches.length) {
            previousHighlightLayers = matches;
            previousHighlightGroup = targetLayer;
            if (bounds.isValid())
                map.fitBounds(bounds, { padding: [50, 50], maxZoom: 18 });
            matches[0].openPopup();
        } else {
            showRouteMessage('No match found for "' + term + '".', "error");
        }
    }
    function performSearch() {
        const term = searchInput.value.trim();
        if (!term) {
            showRouteMessage(
                "Please enter a search term or coordinates.",
                "error"
            );
            return;
        }
        if (handleWGS84Search(term) || handleUTMSearch(term)) return;
        handleAttributeSearch(term);
    }
    setupRoutePlannerUI();
	["start", "end"].forEach(kind => {
        const input = document.getElementById(kind + "-address-input");
        if (input) {
            input.addEventListener("input", () => {
                const markerKey = kind === "start" ? "startMarker" : "endMarker";
                if (routingState[markerKey]) {
                    map.removeLayer(routingState[markerKey]);
                    routingState[markerKey] = null;
                    // Reset coordination fields in the UI
                    const fields = endpointFields(kind);
                    if (fields.latitude) fields.latitude.value = "";
                    if (fields.longitude) fields.longitude.value = "";
                }
            });
        }
    });
    document
    .getElementById("set-start-btn")
    .addEventListener("click", function () {
        clearHighlights();
        clearSearchMarkers();
        routingState.activeMode = "start";
        this.style.background = "#e1e5ea";
        document.getElementById("set-end-btn").style.background = "";
        
        // Disable layer clicks so map click goes through
        setDataLayerClicksEnabled(false);
        setRoutingCursor(true);
		
        showRouteMessage(
            "Click the exact start position on the map. The marker will stay where you click.",
            "info"
        );
    });
document
    .getElementById("set-end-btn")
    .addEventListener("click", function () {
        clearHighlights();
        clearSearchMarkers();
        routingState.activeMode = "end";
        this.style.background = "#e1e5ea";
        document.getElementById("set-start-btn").style.background = "";
        
        // Disable layer clicks
        setDataLayerClicksEnabled(false);
		setRoutingCursor(true);
        
        showRouteMessage(
            "Click the exact destination position on the map. The marker will stay where you click.",
            "info"
        );
    });
    document
        .getElementById("calculate-route-btn")
        .addEventListener("click", calculateAndDisplayRoute);
    document
        .getElementById("clear-route-btn")
        .addEventListener("click", clearCalculatedRouteUI);
    layerSelect.addEventListener("change", () => {
        clearHighlights();
        updateDropdowns();
        searchInput.value = "";
    });
    attributeSelect.addEventListener("change", () => {
        clearHighlights();
        updateDatalist();
        searchInput.value = "";
        searchInput.dispatchEvent(new Event("input"));
    });
    searchInput.addEventListener("input", updateSuggestions);
    searchButton.addEventListener("click", performSearch);
    searchInput.addEventListener("keydown", (event) => {
        if (event.key === "Enter") {
            event.preventDefault();
            performSearch();
        }
    });
    document
        .getElementById("full-extent-btn")
        .addEventListener("click", () =>
            map.fitBounds(boundaryLayer.getBounds())
        );
    map.on("zoomend moveend", () => {
        const zoom = map.getZoom();
        nasLayer.eachLayer((layer) => {
            if (layer.getTooltip && layer.getTooltip())
                zoom >= 17 ? layer.openTooltip() : layer.closeTooltip();
        });
    });
    window.addEventListener("resize", () => map.invalidateSize());
    updateDropdowns();
}
