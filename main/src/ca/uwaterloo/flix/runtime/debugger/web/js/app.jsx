var PointsTo = {
    attributes: ["localVal", "value"],
    rows: [
        [1, "/ParityAnalysis::Parity.Odd(())"],
        [2, "/ParityAnalysis::Parity.Even(())"],
        [3, "/ParityAnalysis::Parity.Odd(())"],
        [7, "/ParityAnalysis::Parity.Odd(())"],
        [8, "/ParityAnalysis::Parity.Top(())"]
    ]
};

var SumOp = {
    attributes: ["localVal", "value"],
    rows: [
        [1, "Buba"],
    ]
};

var Indexes = {
    rows: [
        ["{a}", "423422423"],
        ["{a, b, c}", "423423432423"]
    ]
};

var Relations = ["SumOp"];
var Lattices = ["VarPointsTo"];

/**
 * Main Application entry point.
 */
var App = React.createClass({

    getInitiateState: function () {
        return {};
    },

    changePage: function (page) {
        console.log(page)
    },

    render: function () {
        return (
            <div>
                <Menu changePage={this.changePage} relations={Relations} lattices={Lattices}/>

                <RelationPage name="VarPointsTo" table={PointsTo}/>
            </div>
        );
    }
});

/**
 * Menu component.
 */
var Menu = React.createClass({
    propTypes: {
        changePage: React.PropTypes.func.isRequired,
        relations: React.PropTypes.array.isRequired,
        lattices: React.PropTypes.array.isRequired
    },

    render: function () {
        return (
            <nav className="navbar navbar-default">
                <div className="container-fluid">
                    <div className="navbar-header">
                        <a className="navbar-brand" href="#">Flix Debugger</a>
                    </div>

                    <ul className="nav navbar-nav">
                        <li className="dropdown">
                            <a href="#" className="dropdown-toggle" data-toggle="dropdown">
                                Minimal Model <span className="caret"></span>
                            </a>
                            <ul className="dropdown-menu">
                                {this.props.relations.map(relation => {
                                    return <li key={relation} onClick={() => this.props.changePage({relation})}>
                                        <a href="#">{relation}</a>
                                    </li>
                                })}

                                <li role="separator" className="divider"></li>

                                {this.props.lattices.map(lattice => {
                                    return <li key={lattice}>
                                        <a href="#">{lattice}</a>
                                    </li>
                                })}
                            </ul>
                        </li>
                    </ul>

                    <ul className="nav navbar-nav">
                        <li className="dropdown">
                            <a href="#" className="dropdown-toggle" data-toggle="dropdown">
                                Performance
                                <className className="caret"></className>
                            </a>
                            <ul className="dropdown-menu">
                                <li><a href="">Phases</a></li>
                                <li><a href="">Indexes</a></li>
                                <li><a href="">Queries</a></li>
                            </ul>
                        </li>
                    </ul>

                    <ul className="nav navbar-nav navbar-right">
                        <li className="bg-success">
                            <a href="#"><span className="glyphicon glyphicon-fire"></span> Running</a>
                        </li>

                        <li>
                            <a href="#"> <span className="glyphicon glyphicon-refresh"></span> Refresh</a>
                        </li>
                    </ul>
                </div>
            </nav>
        );
    }
});

/**
 * Relation page.
 */
var RelationPage = React.createClass({
    propTypes: {
        name: React.PropTypes.string.isRequired,
        table: React.PropTypes.object.isRequired
    },
    render: function () {
        return (
            <div>
                <Head name={this.props.name}/>
                <Table table={this.props.table}/>
            </div>
        );
    }
});


/**
 * Head component.
 */
var Head = React.createClass({
    propTypes: {
        name: React.PropTypes.string.isRequired
    },
    render: function () {
        return (
            <div className="page-header">
                <h1>{this.props.name}</h1>
            </div>
        );
    }
});

/**
 * Table component.
 */
var Table = React.createClass({
    propTypes: {
        table: React.PropTypes.shape({
            attributes: React.PropTypes.array.isRequired,
            rows: React.PropTypes.array.isRequired
        })
    },
    render: function () {
        return (
            <table className="table table-striped table-condense">
                <TableHeader attributes={this.props.table.attributes}/>
                <TableBody rows={this.props.table.rows}/>
            </table>
        );
    }
});

/**
 * Table Header component.
 */
var TableHeader = React.createClass({
    propTypes: {
        attributes: React.PropTypes.array.isRequired
    },
    render: function () {
        return (
            <thead>
            <tr>
                {this.props.attributes.map(function (attribute) {
                    return <th key={attribute}>{attribute}</th>
                })}
            </tr>
            </thead>
        );
    }
});

/**
 * Table Body component.
 */
var TableBody = React.createClass({
    propTypes: {
        rows: React.PropTypes.array.isRequired
    },
    render: function () {
        return (
            <tbody>
            {this.props.rows.map(function (row) {
                return <TableRow key={row} row={row}/>
            })}
            </tbody>
        );
    }
});

/**
 * Table Row component.
 */
var TableRow = React.createClass({
    propTypes: {
        row: React.PropTypes.array.isRequired
    },
    render: function () {
        return (
            <tr>
                {this.props.row.map(function (elm) {
                    return <td key={elm}>{elm}</td>
                })}
            </tr>
        );
    }
});


/**
 * Render app when the page is ready.
 */
$(document).ready(function () {
    var root = document.getElementById("container");
    ReactDOM.render(React.createElement(App, null), root);
});
