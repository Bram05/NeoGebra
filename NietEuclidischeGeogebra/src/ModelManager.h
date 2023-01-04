#pragma once
#include "Model.h"

class ModelManager {
private:
	std::shared_ptr<Model> m_Model;

public:
	ModelManager();
	~ModelManager();

	void SetModel(unsigned int pointIdentifiers,
		const Equation& pointDef,
		unsigned int lineIdentifiers,
		const Equation& lineDef,
		const Equation& incidenceConstr,
		const Equation& betweennessConstr = { {}, "" }) 
	{ 
		m_Model = std::make_shared<Model>(pointIdentifiers, pointDef, lineIdentifiers, lineDef, incidenceConstr, betweennessConstr);
	}

	std::shared_ptr<Model> GetModel() { return m_Model; }
};